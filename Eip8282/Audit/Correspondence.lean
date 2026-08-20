import Std.Data.TreeMap.Lemmas
import Eip8282.Audit.Step
import Eip8282.Audit.WellFormed

/-!
CFG correspondence between the pinned runtimes and `Model.userCall` /
`Model.systemCall` (F4, attempt B: system path).

This is **not** a reduction of `EvmYul.EVM.X` / `Ξ`. F3 already showed that
the opening `JUMPI` lands at `read_requests` iff the caller is `SYSTEM_ADDR`.
This module extends a storage-aware CFG stepper through the system-path
blocks `read_requests` (clamp), `update_head` / `reset_queue`, and
`update_excess` / `store_excess`.

The `accum_loop` body (per-item `SLOAD`/`MSTORE` encode) is **not** reduced
to `Ξ`. FIFO pointer updates are a named definition matching
`Model.systemCall` (`nextHead` / `nextTail` / `applyDrainPointers`); CFG hops
cover the HEAD/TAIL `SSTORE`s. Return-buffer encoding is left to D3.

Load-bearing `∀` facts under `WellFormed`, `isSystemCaller`, and
`gas ≥ 30_000_000`:

* the modelled system blocks never CFG-revert (matches `system_always_succeeds`);
* `SLOT_COUNT` is stored `0`;
* excess matches `Model.nextExcess` (assembly `GT`; on-target both sides `0`).
-/

namespace Eip8282.Audit.Correspondence

open EvmYul
open EvmYul.EVM
open EvmYul.Operation
open Eip8282.Audit.Model
open Eip8282.Audit.WellFormed
open Eip8282.Audit.Step
open Eip8282.Audit.Jumpdests
open Eip8282.Audit.Bytecode
open GasConstants

set_option maxRecDepth 20000
set_option linter.dupNamespace false

/-! ## Transitive `Ord` for storage maps

`Storage` is `Std.TreeMap UInt256 UInt256 compare`. The `getD_insert*` lemmas
need `Std.TransCmp`. -/

theorem uint256_le_antisymm {x y : UInt256} (h₁ : x ≤ y) (h₂ : y ≤ x) : x = y := by
  rcases x with ⟨xv⟩
  rcases y with ⟨yv⟩
  exact congrArg UInt256.mk (le_antisymm h₁ h₂)

theorem uint256_le_total (x y : UInt256) : x ≤ y ∨ y ≤ x := by
  rcases x with ⟨xv⟩
  rcases y with ⟨yv⟩
  exact le_total xv yv

theorem uint256_not_le_iff_lt {x y : UInt256} : ¬ x ≤ y ↔ y < x := by
  rcases x with ⟨xv⟩
  rcases y with ⟨yv⟩
  change ¬ (xv ≤ yv) ↔ yv < xv
  omega

theorem ordering_then_eq (o : Ordering) : o.then Ordering.eq = o := by
  cases o <;> rfl

theorem uint256_compare_eq_val (a b : UInt256) :
    compare a b = compare a.val b.val := by
  rcases a with ⟨av⟩
  rcases b with ⟨bv⟩
  exact ordering_then_eq (compare av bv)

instance : Std.TransOrd UInt256 where
  eq_swap {a b} := by
    rw [uint256_compare_eq_val, uint256_compare_eq_val]
    exact Std.OrientedOrd.eq_swap (α := Fin UInt256.size) (a := a.val) (b := b.val)
  isLE_trans {a b c} h₁ h₂ := by
    rw [uint256_compare_eq_val] at h₁ h₂ ⊢
    exact Std.TransOrd.isLE_trans (α := Fin UInt256.size) (a := a.val) (b := b.val) (c := c.val) h₁ h₂

instance : Std.LawfulEqOrd UInt256 where
  eq_of_compare {a b} h := by
    rw [uint256_compare_eq_val] at h
    have hv : a.val = b.val := Std.LawfulEqOrd.eq_of_compare (α := Fin UInt256.size) h
    rcases a with ⟨av⟩
    rcases b with ⟨bv⟩
    cases hv
    rfl

/-! ## User / system gate (F3 corollary)

Both sides of the correspondence: a system caller is at `read_requests` after
the opening `JUMPI`, and a user caller is not. CFG-level; not a reduction of
`X`. -/

theorem deposit_system_iff_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    isSystemCaller caller ↔ m.pc = Deposit.read_requests :=
  (deposit_caller_gate caller gas hgas h).1.symm

theorem deposit_user_iff_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    isUserCaller caller ↔ m.pc = depositUserPc :=
  (deposit_caller_gate caller gas hgas h).2.1.symm

theorem exit_system_iff_read_requests (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    isSystemCaller caller ↔ m.pc = Exit.read_requests :=
  (exit_caller_gate caller gas hgas h).1.symm

theorem exit_user_iff_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    isUserCaller caller ↔ m.pc = exitUserPc :=
  (exit_caller_gate caller gas hgas h).2.1.symm

/-- System callers never fall through to the user `PUSH0`. -/
theorem deposit_system_not_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (hsys : isSystemCaller caller) {m : CfgState}
    (h : runGatePrefix depositOpening caller depositJumpdests gas = .ok m) :
    m.pc ≠ depositUserPc := by
  intro hp
  have := (deposit_caller_gate caller gas hgas h).2.1.mp hp
  exact this hsys

theorem exit_system_not_userPc (caller : UInt256) (gas : Nat)
    (hgas : gas ≥ prefixGasBound) (hsys : isSystemCaller caller) {m : CfgState}
    (h : runGatePrefix exitOpening caller exitJumpdests gas = .ok m) :
    m.pc ≠ exitUserPc := by
  intro hp
  have := (exit_caller_gate caller gas hgas h).2.1.mp hp
  exact this hsys

theorem deposit_read_requests_eq : Deposit.read_requests = 284 := rfl
theorem exit_read_requests_eq : Exit.read_requests = 225 := rfl

/-! ## Named FIFO (matches `Model.systemCall`; not a `Ξ` claim)

`accum_loop` is skipped. These are the pointer writes `update_head` /
`reset_queue` implement, and the logical queue they induce. Stale slots are
unconstrained (F2). -/

def drainCount (kind : Kind) (σ : Storage) : Nat :=
  min (queueTail σ - queueHead σ) (capOf kind)

/-- Full drain (length ≤ cap) zeroes both pointers; partial drain advances
`HEAD` by `cap` and leaves `TAIL` unchanged. -/
def nextHead (kind : Kind) (σ : Storage) : Nat :=
  if queueTail σ - queueHead σ ≤ capOf kind then 0
  else queueHead σ + capOf kind

def nextTail (kind : Kind) (σ : Storage) : Nat :=
  if queueTail σ - queueHead σ ≤ capOf kind then 0
  else queueTail σ

def recordSizeOf : Kind → Nat
  | .deposit => 184
  | .exit => 68

def storeWord (σ : Storage) (slot v : Nat) : Storage :=
  σ.insert (UInt256.ofNat slot) (UInt256.ofNat v)

def storeWordU (σ : Storage) (slot : Nat) (v : UInt256) : Storage :=
  σ.insert (UInt256.ofNat slot) v

/-- Control-slot image after the system `update_head` / `reset_queue` writes. -/
def applyDrainPointers (kind : Kind) (σ : Storage) : Storage :=
  storeWord (storeWord σ QUEUE_HEAD (nextHead kind σ)) QUEUE_TAIL (nextTail kind σ)

/-- Control-slot image after `store_excess`: new excess, count 0, drained pointers. -/
def applySystemStorage (kind : Kind) (σ : Storage) (calldataNonempty : Bool) : Storage :=
  let σ' := applyDrainPointers kind σ
  storeWord (storeWordU σ' SLOT_EXCESS
      (UInt256.ofNat (nextExcess (toModel kind σ 0) calldataNonempty)))
    SLOT_COUNT 0

theorem capOf_deposit : capOf .deposit = 64 := rfl
theorem capOf_exit : capOf .exit = 16 := rfl
theorem targetOf_deposit : targetOf .deposit = 8 := rfl
theorem targetOf_exit : targetOf .exit = 2 := rfl

theorem drainCount_eq_min (kind : Kind) (σ : Storage) :
    drainCount kind σ = min (queueTail σ - queueHead σ) (capOf kind) :=
  rfl

theorem drainCount_le_cap (kind : Kind) (σ : Storage) :
    drainCount kind σ ≤ capOf kind :=
  Nat.min_le_right _ _

theorem drainCount_le_length {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    drainCount kind σ ≤ (queueOf kind σ).length := by
  rw [queueOf_length wf]
  exact Nat.min_le_left _ _

/-- Full drain zeroes HEAD. -/
theorem nextHead_full {kind : Kind} {σ : Storage}
    (h : queueTail σ - queueHead σ ≤ capOf kind) :
    nextHead kind σ = 0 :=
  if_pos h

/-- Partial drain advances HEAD by cap. -/
theorem nextHead_partial {kind : Kind} {σ : Storage}
    (h : ¬ queueTail σ - queueHead σ ≤ capOf kind) :
    nextHead kind σ = queueHead σ + capOf kind :=
  if_neg h

theorem nextTail_full {kind : Kind} {σ : Storage}
    (h : queueTail σ - queueHead σ ≤ capOf kind) :
    nextTail kind σ = 0 :=
  if_pos h

theorem nextTail_partial {kind : Kind} {σ : Storage}
    (h : ¬ queueTail σ - queueHead σ ≤ capOf kind) :
    nextTail kind σ = queueTail σ :=
  if_neg h

/-! ## `UInt256` helpers -/

theorem toNat_ofNat_of_lt {n : Nat} (h : n < UInt256.size) :
    (UInt256.ofNat n).toNat = n := by
  unfold UInt256.ofNat UInt256.toNat
  exact Nat.mod_eq_of_lt h

theorem two_pow_64_lt_size : 2 ^ 64 < UInt256.size := by
  unfold UInt256.size
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 64 < 256)

theorem lt_size_of_lt_two_pow_64 {n : Nat} (h : n < 2 ^ 64) : n < UInt256.size :=
  Nat.lt_trans h two_pow_64_lt_size

theorem toNat_ofNat_of_lt_64 {n : Nat} (h : n < 2 ^ 64) :
    (UInt256.ofNat n).toNat = n :=
  toNat_ofNat_of_lt (lt_size_of_lt_two_pow_64 h)

theorem ofNat_inj_of_lt {a b : Nat} (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : UInt256.ofNat a = UInt256.ofNat b) : a = b := by
  have := congrArg UInt256.toNat h
  simp only [toNat_ofNat_of_lt ha, toNat_ofNat_of_lt hb] at this
  exact this

private theorem not_lt_of_ge {a b : Nat} (h : a ≥ b) : ¬ a < b :=
  Nat.not_lt.mpr h

theorem bne_one_zero' : (UInt256.ofNat 1 != UInt256.ofNat 0) = true := by
  decide

theorem bne_zero_zero' : (UInt256.ofNat 0 != UInt256.ofNat 0) = false := by
  decide

theorem eq_one_of_eq' {a b : UInt256} (h : a = b) :
    UInt256.eq a b = UInt256.ofNat 1 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

theorem eq_zero_of_ne' {a b : UInt256} (h : a ≠ b) :
    UInt256.eq a b = UInt256.ofNat 0 := by
  simp [UInt256.eq, UInt256.fromBool, Bool.toUInt256, h]

theorem gt_one_of_gt {a b : UInt256} (h : a > b) :
    UInt256.gt a b = UInt256.ofNat 1 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

theorem gt_zero_of_nle {a b : UInt256} (h : ¬ a > b) :
    UInt256.gt a b = UInt256.ofNat 0 := by
  simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, h]

/-! ## Storage writes -/

theorem loadU256_insert_self (σ : Storage) (slot : Nat) (v : UInt256) :
    loadU256 (σ.insert (UInt256.ofNat slot) v) slot = v := by
  unfold loadU256
  exact Std.TreeMap.getD_insert_self

theorem loadNat_insert_self (σ : Storage) (slot v : Nat) (hv : v < UInt256.size) :
    loadNat (σ.insert (UInt256.ofNat slot) (UInt256.ofNat v)) slot = v := by
  unfold loadNat
  rw [loadU256_insert_self]
  exact toNat_ofNat_of_lt hv

theorem loadU256_insert_of_ne (σ : Storage) (k : Nat) (v : UInt256) (slot : Nat)
    (hne : UInt256.ofNat k ≠ UInt256.ofNat slot) :
    loadU256 (σ.insert (UInt256.ofNat k) v) slot = loadU256 σ slot := by
  unfold loadU256
  rw [Std.TreeMap.getD_insert]
  split_ifs with hcmp
  · have : UInt256.ofNat k = UInt256.ofNat slot :=
      Std.LawfulEqOrd.eq_of_compare (α := UInt256) hcmp
    exact absurd this hne
  · rfl

theorem ofNat_slot_ne :
    UInt256.ofNat 0 ≠ UInt256.ofNat 1 ∧
    UInt256.ofNat 0 ≠ UInt256.ofNat 2 ∧
    UInt256.ofNat 0 ≠ UInt256.ofNat 3 ∧
    UInt256.ofNat 1 ≠ UInt256.ofNat 0 ∧
    UInt256.ofNat 1 ≠ UInt256.ofNat 2 ∧
    UInt256.ofNat 1 ≠ UInt256.ofNat 3 ∧
    UInt256.ofNat 2 ≠ UInt256.ofNat 0 ∧
    UInt256.ofNat 2 ≠ UInt256.ofNat 1 ∧
    UInt256.ofNat 2 ≠ UInt256.ofNat 3 ∧
    UInt256.ofNat 3 ≠ UInt256.ofNat 0 ∧
    UInt256.ofNat 3 ≠ UInt256.ofNat 1 ∧
    UInt256.ofNat 3 ≠ UInt256.ofNat 2 := by
  decide

theorem slotCount_after_zero (σ : Storage) (exc : UInt256) :
    slotCount (storeWord (storeWordU σ SLOT_EXCESS exc) SLOT_COUNT 0) = 0 := by
  unfold slotCount storeWord SLOT_COUNT
  exact loadNat_insert_self _ _ _ (by decide)

theorem slotExcess_after_store (σ : Storage) (exc : UInt256) :
    loadU256 (storeWord (storeWordU σ SLOT_EXCESS exc) SLOT_COUNT 0) SLOT_EXCESS = exc := by
  unfold storeWord storeWordU SLOT_EXCESS SLOT_COUNT
  rw [loadU256_insert_of_ne]
  · exact loadU256_insert_self _ _ _
  · exact ofNat_slot_ne.2.2.2.1

/-! ## `nextExcess` vs assembly `GT`

Model uses `≥`; assembly uses `GT`. When `excess + count = target` both
sides yield `0`. -/

def asmNextExcess (kind : Kind) (excess count : Nat) (calldataNonempty : Bool) : Nat :=
  if calldataNonempty then inhibitor
  else if excess = inhibitor then 0
  else if excess + count > targetOf kind then excess + count - targetOf kind
  else 0

/-- Nat-level agreement: `≥` vs `GT` only differ on equality, where both are `0`. -/
theorem nextExcess_eq_asm (s : Model.State) (b : Bool) :
    nextExcess s b = asmNextExcess s.kind s.storedExcess s.count b := by
  unfold nextExcess asmNextExcess inhibited
  cases b with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases hinh : s.storedExcess = inhibitor
    · simp [hinh]
    · simp [hinh]
      split_ifs <;> omega

theorem nextExcess_nonempty (s : Model.State) :
    nextExcess s true = inhibitor := by
  unfold nextExcess; simp

theorem nextExcess_inhibited_empty (s : Model.State) (h : inhibited s = true) :
    nextExcess s false = 0 := by
  unfold nextExcess
  simp [h]

theorem nextExcess_fold (s : Model.State) (h : inhibited s = false) :
    nextExcess s false =
      if s.storedExcess + s.count ≥ targetOf s.kind then
        s.storedExcess + s.count - targetOf s.kind
      else 0 := by
  unfold nextExcess
  simp [h]

/-! ## FIFO algebraic correspondence (named; not `Ξ`) -/

theorem ofNat_ne_of_ne {a b : Nat} (ha : a < UInt256.size) (hb : b < UInt256.size)
    (h : a ≠ b) : UInt256.ofNat a ≠ UInt256.ofNat b := by
  intro heq
  exact h (ofNat_inj_of_lt ha hb heq)

theorem drop_map_range {α} (n k : Nat) (f : Nat → α) (_hk : k ≤ n) :
    ((List.range n).map f).drop k =
      (List.range (n - k)).map (fun i => f (k + i)) := by
  apply List.ext_getElem
  · simp [List.length_drop, List.length_map, List.length_range]
  · intro i hi hi'
    simp [List.getElem_drop, List.getElem_map, List.getElem_range]

theorem queueOf_drop_eq_min {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    (queueOf kind σ).drop (capOf kind) =
      (queueOf kind σ).drop (drainCount kind σ) := by
  have hlen := queueOf_length wf
  unfold drainCount
  by_cases h : queueTail σ - queueHead σ ≤ capOf kind
  · have hlen' : (queueOf kind σ).length ≤ capOf kind := by omega
    rw [Nat.min_eq_left h, List.drop_eq_nil_of_le hlen']
    have : (queueOf kind σ).length ≤ queueTail σ - queueHead σ := by omega
    rw [List.drop_eq_nil_of_le this]
  · have : capOf kind ≤ queueTail σ - queueHead σ := Nat.le_of_not_ge h
    rw [Nat.min_eq_right this]

/-- After writing the named drain pointers, the logical FIFO is `queue.drop cap`,
provided item words (slots ≥ `QUEUE_OFFSET`) are unchanged. That proviso is the
F2 stale-slot discipline: `update_head` / `reset_queue` only `SSTORE` slots 2–3.
This is not a `Ξ` claim about `accum_loop`. -/
theorem fifo_matches_model {kind : Kind} {σ : Storage} (wf : WellFormed kind σ)
    (hhead : queueHead (applyDrainPointers kind σ) = nextHead kind σ)
    (htail : queueTail (applyDrainPointers kind σ) = nextTail kind σ)
    (hitems : ∀ idx, decodeItem kind (applyDrainPointers kind σ) idx =
      decodeItem kind σ idx) :
    queueOf kind (applyDrainPointers kind σ) = (queueOf kind σ).drop (capOf kind) := by
  have hle := head_le_tail wf
  have hlen := queueOf_length wf
  by_cases hfull : queueTail σ - queueHead σ ≤ capOf kind
  · have hnh : nextHead kind σ = 0 := if_pos hfull
    have hnt : nextTail kind σ = 0 := if_pos hfull
    have hqnew : queueOf kind (applyDrainPointers kind σ) = [] := by
      unfold queueOf
      rw [hhead, htail, hnh, hnt]
      simp
    have hqold : (queueOf kind σ).drop (capOf kind) = [] :=
      List.drop_eq_nil_of_le (by omega)
    simp [hqnew, hqold]
  · have hcap : capOf kind ≤ queueTail σ - queueHead σ := Nat.le_of_not_ge hfull
    have hnh : nextHead kind σ = queueHead σ + capOf kind := if_neg hfull
    have hnt : nextTail kind σ = queueTail σ := if_neg hfull
    have hnewle : queueHead σ + capOf kind ≤ queueTail σ := by omega
    have hleft : queueOf kind (applyDrainPointers kind σ) =
        (List.range (queueTail σ - (queueHead σ + capOf kind))).map
          (fun i => decodeItem kind σ (queueHead σ + capOf kind + i)) := by
      unfold queueOf
      rw [hhead, htail, hnh, hnt]
      simp [hnewle, hitems]
    have hright : (queueOf kind σ).drop (capOf kind) =
        (List.range (queueTail σ - queueHead σ - capOf kind)).map
          (fun i => decodeItem kind σ (queueHead σ + (capOf kind + i))) := by
      have hq : queueOf kind σ =
          (List.range (queueTail σ - queueHead σ)).map
            (fun i => decodeItem kind σ (queueHead σ + i)) := by
        unfold queueOf; simp [hle]
      rw [hq, drop_map_range _ _ _ hcap]
    have hlenr : queueTail σ - (queueHead σ + capOf kind) =
        queueTail σ - queueHead σ - capOf kind := by omega
    rw [hleft, hright, hlenr]
    congr 1
    funext i
    simp [Nat.add_assoc]

/-! ## System-path CFG stepper

Storage-aware extension of F3's `cfgStep`. Covers the system-path instruction
set (`SLOAD`/`SSTORE`, arithmetic, `DUP`/`SWAP`, `JUMP`/`JUMPI`,
`CALLDATASIZE`, `RETURN`). Gas is a conservative schedule: every `SLOAD` is
cold (`Gcoldsload`), every `SSTORE` is `Gsset`. That only makes the
`gas ≥ 30_000_000` hypothesis harder. -/

inductive SysError where
  | outOfGas
  | stackUnderflow
  | badJump
  | unexpectedOpcode
  | revert
  deriving DecidableEq, Repr

structure SysCfg where
  pc : Nat
  stack : List UInt256
  gas : Nat
  storage : Storage
  calldataNonempty : Bool
  halted : Bool := false
  returnSize : Nat := 0
  deriving Inhabited

def sysBlockGas : Nat := 100000

/-- Conservative bound for the `store_excess` tail (two cold `SSTORE`s). -/
def sysStoreGas : Nat := 50000

theorem sysBlockGas_le_campaign : sysBlockGas ≤ campaignGasBound := by
  decide

theorem sysStoreGas_le_block : sysStoreGas ≤ sysBlockGas := by
  decide

/-- Remaining gas after `used` cheap/expensive ops still covers `need`. -/
theorem gas_remaining {gas used need : Nat}
    (hgas : gas ≥ sysBlockGas) (hsum : used + need ≤ sysBlockGas) :
    gas - used ≥ need := by
  simp [sysBlockGas] at hgas hsum ⊢
  omega

theorem uint256_add_sub_cancel (a b : UInt256) : a + (b - a) = b := by
  rcases a with ⟨av⟩
  rcases b with ⟨bv⟩
  change UInt256.mk (av + (bv - av)) = UInt256.mk bv
  rw [add_comm, sub_add_cancel]

/-- Avoid `{ s with stack := x :: xs }` (Lean 4.31 structure-update parser). -/
def sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage := m.storage) : SysCfg :=
  { pc := pc, stack := stack, gas := gas, storage := storage,
    calldataNonempty := m.calldataNonempty, halted := m.halted,
    returnSize := m.returnSize }

def sysHalt (m : SysCfg) (returnSize : Nat) : SysCfg :=
  { pc := m.pc, stack := [], gas := m.gas, storage := m.storage,
    calldataNonempty := m.calldataNonempty, halted := true, returnSize := returnSize }

def cfgStep (op : Nat → Option (Operation .EVM × Option (UInt256 × Nat)))
    (validJumps : Array UInt256) (m : SysCfg) : Except SysError SysCfg :=
  if m.halted then .ok m
  else
    match op m.pc with
    | some (.StackMemFlow .JUMPDEST, none) =>
        if m.gas < Gjumpdest then .error .outOfGas
        else .ok (sysNext m (m.pc + 1) m.stack (m.gas - Gjumpdest))
    | some (.Env .CALLDATASIZE, none) =>
        if m.gas < Gbase then .error .outOfGas
        else
          .ok (sysNext m (m.pc + 1)
                ((if m.calldataNonempty then UInt256.ofNat 1
                  else UInt256.ofNat 0) :: m.stack)
                (m.gas - Gbase))
    | some (.Push .PUSH0, none) =>
        if m.gas < Gbase then .error .outOfGas
        else
          .ok (sysNext m (m.pc + 1) (UInt256.ofNat 0 :: m.stack) (m.gas - Gbase))
    | some (.Push _, some (imm, width)) =>
        if m.gas < Gverylow then .error .outOfGas
        else
          .ok (sysNext m (m.pc + 1 + width) (imm :: m.stack) (m.gas - Gverylow))
    | some (.StopArith .ADD, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) ((a + b) :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.StopArith .SUB, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) ((a - b) :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.StopArith .MUL, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Glow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) ((a * b) :: rest) (m.gas - Glow))
        | _ => .error .stackUnderflow
    | some (.CompBit .GT, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (UInt256.gt a b :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.CompBit .EQ, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (UInt256.eq a b :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.StackMemFlow .POP, none) =>
        match m.stack with
        | _ :: rest =>
            if m.gas < Gbase then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) rest (m.gas - Gbase))
        | _ => .error .stackUnderflow
    | some (.Dup .DUP1, none) =>
        match m.stack with
        | a :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (a :: a :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.Dup .DUP2, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (b :: a :: b :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.Dup .DUP3, none) =>
        match m.stack with
        | a :: b :: c :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (c :: a :: b :: c :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.Exchange .SWAP1, none) =>
        match m.stack with
        | a :: b :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (b :: a :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.Exchange .SWAP2, none) =>
        match m.stack with
        | a :: b :: c :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (c :: b :: a :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.Exchange .SWAP3, none) =>
        match m.stack with
        | a :: b :: c :: d :: rest =>
            if m.gas < Gverylow then .error .outOfGas
            else .ok (sysNext m (m.pc + 1) (d :: b :: c :: a :: rest) (m.gas - Gverylow))
        | _ => .error .stackUnderflow
    | some (.StackMemFlow .SLOAD, none) =>
        match m.stack with
        | slot :: rest =>
            if m.gas < Gcoldsload then .error .outOfGas
            else
              .ok (sysNext m (m.pc + 1)
                    (m.storage.getD slot (UInt256.ofNat 0) :: rest)
                    (m.gas - Gcoldsload))
        | _ => .error .stackUnderflow
    | some (.StackMemFlow .SSTORE, none) =>
        match m.stack with
        | slot :: val :: rest =>
            if m.gas < Gsset then .error .outOfGas
            else
              .ok (sysNext m (m.pc + 1) rest (m.gas - Gsset)
                    (m.storage.insert slot val))
        | _ => .error .stackUnderflow
    | some (.StackMemFlow .JUMP, none) =>
        match m.stack with
        | dest :: rest =>
            if m.gas < Gmid then .error .outOfGas
            else if validJumps.contains dest then
              .ok (sysNext m dest.toNat rest (m.gas - Gmid))
            else
              .error .badJump
        | _ => .error .stackUnderflow
    | some (.StackMemFlow .JUMPI, none) =>
        match m.stack with
        | dest :: cond :: rest =>
            if m.gas < Ghigh then .error .outOfGas
            else if cond != UInt256.ofNat 0 then
              if validJumps.contains dest then
                .ok (sysNext m dest.toNat rest (m.gas - Ghigh))
              else
                .error .badJump
            else
              .ok (sysNext m (m.pc + 1) rest (m.gas - Ghigh))
        | _ => .error .stackUnderflow
    | some (.System .RETURN, none) =>
        match m.stack with
        | _off :: size :: _rest =>
            .ok (sysHalt m size.toNat)
        | _ => .error .stackUnderflow
    | some (.System .REVERT, none) => .error .revert
    | _ => .error .unexpectedOpcode


/-- Iterate `cfgStep` until fuel or `halted`. Explicit fuel; not `X`. -/
def runSys (op : Nat → Option (Operation .EVM × Option (UInt256 × Nat)))
    (validJumps : Array UInt256) : Nat → SysCfg → Except SysError SysCfg
  | 0, m => .ok m
  | n + 1, m =>
      if m.halted then .ok m
      else
        match cfgStep op validJumps m with
        | .error e => .error e
        | .ok m' => runSys op validJumps n m'

theorem runSys_succ {op jumps n m m'}
    (hh : m.halted = false)
    (h : cfgStep op jumps m = .ok m') :
    runSys op jumps (n + 1) m = runSys op jumps n m' := by
  simp [runSys, hh, h]

/-! ## Jumpdest `contains` (F1 tables; do not re-enter `D_J_aux`) -/

theorem deposit_contains_nat (n : Nat) (hn : n ∈ depositJumpdestNats)
    (hbeq : (UInt256.ofNat n == UInt256.ofNat n) = true) :
    depositJumpdests.contains (UInt256.ofNat n) = true :=
  (Array.contains_iff_exists_mem_beq).mpr ⟨UInt256.ofNat n, mem_depositJumpdests_of_mem_nats hn, hbeq⟩

theorem exit_contains_nat (n : Nat) (hn : n ∈ exitJumpdestNats)
    (hbeq : (UInt256.ofNat n == UInt256.ofNat n) = true) :
    exitJumpdests.contains (UInt256.ofNat n) = true :=
  (Array.contains_iff_exists_mem_beq).mpr ⟨UInt256.ofNat n, mem_exitJumpdests_of_mem_nats hn, hbeq⟩

theorem deposit_system_jumpdests :
    depositJumpdests.contains (UInt256.ofNat Deposit.set_inhibitor) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.zero_excess) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.compute_excess) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.store_excess) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.reset_queue) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.update_excess) = true ∧
    depositJumpdests.contains (UInt256.ofNat Deposit.begin_loop) = true := by
  refine ⟨deposit_contains_nat _ (by decide) rfl, deposit_contains_nat _ (by decide) rfl,
    deposit_contains_nat _ (by decide) rfl, deposit_contains_nat _ (by decide) rfl,
    deposit_contains_nat _ (by decide) rfl, deposit_contains_nat _ (by decide) rfl,
    deposit_contains_nat _ (by decide) rfl⟩

theorem exit_system_jumpdests :
    exitJumpdests.contains (UInt256.ofNat Exit.set_inhibitor) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.zero_excess) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.compute_excess) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.store_excess) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.reset_queue) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.update_excess) = true ∧
    exitJumpdests.contains (UInt256.ofNat Exit.begin_loop) = true := by
  refine ⟨exit_contains_nat _ (by decide) rfl, exit_contains_nat _ (by decide) rfl,
    exit_contains_nat _ (by decide) rfl, exit_contains_nat _ (by decide) rfl,
    exit_contains_nat _ (by decide) rfl, exit_contains_nat _ (by decide) rfl,
    exit_contains_nat _ (by decide) rfl⟩

theorem toNat_named_deposit :
    (UInt256.ofNat Deposit.set_inhibitor).toNat = Deposit.set_inhibitor ∧
    (UInt256.ofNat Deposit.zero_excess).toNat = Deposit.zero_excess ∧
    (UInt256.ofNat Deposit.compute_excess).toNat = Deposit.compute_excess ∧
    (UInt256.ofNat Deposit.store_excess).toNat = Deposit.store_excess ∧
    (UInt256.ofNat Deposit.reset_queue).toNat = Deposit.reset_queue ∧
    (UInt256.ofNat Deposit.update_excess).toNat = Deposit.update_excess ∧
    (UInt256.ofNat Deposit.begin_loop).toNat = Deposit.begin_loop := by
  decide

theorem toNat_named_exit :
    (UInt256.ofNat Exit.set_inhibitor).toNat = Exit.set_inhibitor ∧
    (UInt256.ofNat Exit.zero_excess).toNat = Exit.zero_excess ∧
    (UInt256.ofNat Exit.compute_excess).toNat = Exit.compute_excess ∧
    (UInt256.ofNat Exit.store_excess).toNat = Exit.store_excess ∧
    (UInt256.ofNat Exit.reset_queue).toNat = Exit.reset_queue ∧
    (UInt256.ofNat Exit.update_excess).toNat = Exit.update_excess ∧
    (UInt256.ofNat Exit.begin_loop).toNat = Exit.begin_loop := by
  decide



/-! ## Opcode table for `update_excess` … `RETURN`

Pinned by the small hex facts below (F3-style `rfl` on `fromHex` of a
few bytes). The table is what the CFG stepper uses, so JUMP targets stay
absolute runtime PCs without reducing a 124-byte `fromHex`. -/

def depositExcessOp (pc : Nat) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  if pc = 500 then some (.JUMPDEST, none)
  else if pc = 501 then some (.CALLDATASIZE, none)
  else if pc = 502 then some (.PUSH2, some (UInt256.ofNat 578, 2))
  else if pc = 505 then some (.JUMPI, none)
  else if pc = 506 then some (.PUSH0, none)
  else if pc = 507 then some (.SLOAD, none)
  else if pc = 508 then some (.PUSH1, some (UInt256.ofNat 1, 1))
  else if pc = 510 then some (.SLOAD, none)
  else if pc = 511 then some (.DUP2, none)
  else if pc = 512 then some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  else if pc = 545 then some (.EQ, none)
  else if pc = 546 then some (.PUSH2, some (UInt256.ofNat 560, 2))
  else if pc = 549 then some (.JUMPI, none)
  else if pc = 550 then some (.PUSH1, some (UInt256.ofNat 8, 1))
  else if pc = 552 then some (.DUP3, none)
  else if pc = 553 then some (.DUP3, none)
  else if pc = 554 then some (.ADD, none)
  else if pc = 555 then some (.GT, none)
  else if pc = 556 then some (.PUSH2, some (UInt256.ofNat 568, 2))
  else if pc = 559 then some (.JUMPI, none)
  else if pc = 560 then some (.JUMPDEST, none)
  else if pc = 561 then some (.POP, none)
  else if pc = 562 then some (.POP, none)
  else if pc = 563 then some (.PUSH0, none)
  else if pc = 564 then some (.PUSH2, some (UInt256.ofNat 612, 2))
  else if pc = 567 then some (.JUMP, none)
  else if pc = 568 then some (.JUMPDEST, none)
  else if pc = 569 then some (.ADD, none)
  else if pc = 570 then some (.PUSH1, some (UInt256.ofNat 8, 1))
  else if pc = 572 then some (.SWAP1, none)
  else if pc = 573 then some (.SUB, none)
  else if pc = 574 then some (.PUSH2, some (UInt256.ofNat 612, 2))
  else if pc = 577 then some (.JUMP, none)
  else if pc = 578 then some (.JUMPDEST, none)
  else if pc = 579 then some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  else if pc = 612 then some (.JUMPDEST, none)
  else if pc = 613 then some (.PUSH0, none)
  else if pc = 614 then some (.SSTORE, none)
  else if pc = 615 then some (.PUSH0, none)
  else if pc = 616 then some (.PUSH1, some (UInt256.ofNat 1, 1))
  else if pc = 618 then some (.SSTORE, none)
  else if pc = 619 then some (.PUSH1, some (UInt256.ofNat 184, 1))
  else if pc = 621 then some (.MUL, none)
  else if pc = 622 then some (.PUSH0, none)
  else if pc = 623 then some (.RETURN, none)
  else none

def exitExcessOp (pc : Nat) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  if pc = 330 then some (.JUMPDEST, none)
  else if pc = 331 then some (.CALLDATASIZE, none)
  else if pc = 332 then some (.PUSH2, some (UInt256.ofNat 408, 2))
  else if pc = 335 then some (.JUMPI, none)
  else if pc = 336 then some (.PUSH0, none)
  else if pc = 337 then some (.SLOAD, none)
  else if pc = 338 then some (.PUSH1, some (UInt256.ofNat 1, 1))
  else if pc = 340 then some (.SLOAD, none)
  else if pc = 341 then some (.DUP2, none)
  else if pc = 342 then some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  else if pc = 375 then some (.EQ, none)
  else if pc = 376 then some (.PUSH2, some (UInt256.ofNat 390, 2))
  else if pc = 379 then some (.JUMPI, none)
  else if pc = 380 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 382 then some (.DUP3, none)
  else if pc = 383 then some (.DUP3, none)
  else if pc = 384 then some (.ADD, none)
  else if pc = 385 then some (.GT, none)
  else if pc = 386 then some (.PUSH2, some (UInt256.ofNat 398, 2))
  else if pc = 389 then some (.JUMPI, none)
  else if pc = 390 then some (.JUMPDEST, none)
  else if pc = 391 then some (.POP, none)
  else if pc = 392 then some (.POP, none)
  else if pc = 393 then some (.PUSH0, none)
  else if pc = 394 then some (.PUSH2, some (UInt256.ofNat 442, 2))
  else if pc = 397 then some (.JUMP, none)
  else if pc = 398 then some (.JUMPDEST, none)
  else if pc = 399 then some (.ADD, none)
  else if pc = 400 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 402 then some (.SWAP1, none)
  else if pc = 403 then some (.SUB, none)
  else if pc = 404 then some (.PUSH2, some (UInt256.ofNat 442, 2))
  else if pc = 407 then some (.JUMP, none)
  else if pc = 408 then some (.JUMPDEST, none)
  else if pc = 409 then some (.PUSH32, some (UInt256.ofNat inhibitor, 32))
  else if pc = 442 then some (.JUMPDEST, none)
  else if pc = 443 then some (.PUSH0, none)
  else if pc = 444 then some (.SSTORE, none)
  else if pc = 445 then some (.PUSH0, none)
  else if pc = 446 then some (.PUSH1, some (UInt256.ofNat 1, 1))
  else if pc = 448 then some (.SSTORE, none)
  else if pc = 449 then some (.PUSH1, some (UInt256.ofNat 68, 1))
  else if pc = 451 then some (.MUL, none)
  else if pc = 452 then some (.PUSH0, none)
  else if pc = 453 then some (.RETURN, none)
  else none

def depositHeadOp (pc : Nat) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  if pc = 471 then some (.JUMPDEST, none)
  else if pc = 472 then some (.SWAP2, none)
  else if pc = 473 then some (.ADD, none)
  else if pc = 474 then some (.DUP1, none)
  else if pc = 475 then some (.SWAP3, none)
  else if pc = 476 then some (.EQ, none)
  else if pc = 477 then some (.PUSH2, some (UInt256.ofNat 489, 2))
  else if pc = 480 then some (.JUMPI, none)
  else if pc = 481 then some (.SWAP1, none)
  else if pc = 482 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 484 then some (.SSTORE, none)
  else if pc = 485 then some (.PUSH2, some (UInt256.ofNat 500, 2))
  else if pc = 488 then some (.JUMP, none)
  else if pc = 489 then some (.JUMPDEST, none)
  else if pc = 490 then some (.SWAP1, none)
  else if pc = 491 then some (.POP, none)
  else if pc = 492 then some (.PUSH0, none)
  else if pc = 493 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 495 then some (.SSTORE, none)
  else if pc = 496 then some (.PUSH0, none)
  else if pc = 497 then some (.PUSH1, some (UInt256.ofNat 3, 1))
  else if pc = 499 then some (.SSTORE, none)
  else none

def exitHeadOp (pc : Nat) : Option (Operation .EVM × Option (UInt256 × Nat)) :=
  if pc = 301 then some (.JUMPDEST, none)
  else if pc = 302 then some (.SWAP2, none)
  else if pc = 303 then some (.ADD, none)
  else if pc = 304 then some (.DUP1, none)
  else if pc = 305 then some (.SWAP3, none)
  else if pc = 306 then some (.EQ, none)
  else if pc = 307 then some (.PUSH2, some (UInt256.ofNat 319, 2))
  else if pc = 310 then some (.JUMPI, none)
  else if pc = 311 then some (.SWAP1, none)
  else if pc = 312 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 314 then some (.SSTORE, none)
  else if pc = 315 then some (.PUSH2, some (UInt256.ofNat 330, 2))
  else if pc = 318 then some (.JUMP, none)
  else if pc = 319 then some (.JUMPDEST, none)
  else if pc = 320 then some (.SWAP1, none)
  else if pc = 321 then some (.POP, none)
  else if pc = 322 then some (.PUSH0, none)
  else if pc = 323 then some (.PUSH1, some (UInt256.ofNat 2, 1))
  else if pc = 325 then some (.SSTORE, none)
  else if pc = 326 then some (.PUSH0, none)
  else if pc = 327 then some (.PUSH1, some (UInt256.ofNat 3, 1))
  else if pc = 329 then some (.SSTORE, none)
  else none

/-! Ground opcode facts. Hops rewrite `.pc` to a numeral, then use these.
Never `simp [depositExcessOp, nested_sysNext]` — the 50-way `if` chain
hits max recursion depth. -/

theorem pc_sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage) :
    (sysNext m pc stack gas storage).pc = pc := rfl

theorem gas_sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage) :
    (sysNext m pc stack gas storage).gas = gas := rfl

theorem stack_sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage) :
    (sysNext m pc stack gas storage).stack = stack := rfl

theorem storage_sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage) :
    (sysNext m pc stack gas storage).storage = storage := rfl

theorem halted_sysNext (m : SysCfg) (pc : Nat) (stack : List UInt256) (gas : Nat)
    (storage : Storage) :
    (sysNext m pc stack gas storage).halted = m.halted := rfl

theorem hop_of_pc {op : Nat → Option (Operation .EVM × Option (UInt256 × Nat))}
    {m : SysCfg} {pc : Nat} {v : Operation .EVM × Option (UInt256 × Nat)}
    (hpc : m.pc = pc) (hv : op pc = some v) : op m.pc = some v :=
  hpc ▸ hv

theorem depositExcessOp_500 : depositExcessOp 500 = some (.JUMPDEST, none) := rfl
theorem depositExcessOp_501 : depositExcessOp 501 = some (.CALLDATASIZE, none) := rfl
theorem depositExcessOp_502 :
    depositExcessOp 502 = some (.PUSH2, some (UInt256.ofNat 578, 2)) := rfl
theorem depositExcessOp_505 : depositExcessOp 505 = some (.JUMPI, none) := rfl
theorem depositExcessOp_506 : depositExcessOp 506 = some (.PUSH0, none) := rfl
theorem depositExcessOp_578 : depositExcessOp 578 = some (.JUMPDEST, none) := rfl
theorem depositExcessOp_579 :
    depositExcessOp 579 = some (.PUSH32, some (UInt256.ofNat inhibitor, 32)) := rfl
theorem depositExcessOp_612 : depositExcessOp 612 = some (.JUMPDEST, none) := rfl
theorem depositExcessOp_613 : depositExcessOp 613 = some (.PUSH0, none) := rfl
theorem depositExcessOp_614 : depositExcessOp 614 = some (.SSTORE, none) := rfl
theorem depositExcessOp_615 : depositExcessOp 615 = some (.PUSH0, none) := rfl
theorem depositExcessOp_616 :
    depositExcessOp 616 = some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl
theorem depositExcessOp_618 : depositExcessOp 618 = some (.SSTORE, none) := rfl
theorem depositExcessOp_619 :
    depositExcessOp 619 = some (.PUSH1, some (UInt256.ofNat 184, 1)) := rfl
theorem depositExcessOp_621 : depositExcessOp 621 = some (.MUL, none) := rfl
theorem depositExcessOp_622 : depositExcessOp 622 = some (.PUSH0, none) := rfl
theorem depositExcessOp_623 : depositExcessOp 623 = some (.RETURN, none) := rfl

theorem exitExcessOp_330 : exitExcessOp 330 = some (.JUMPDEST, none) := rfl
theorem exitExcessOp_331 : exitExcessOp 331 = some (.CALLDATASIZE, none) := rfl
theorem exitExcessOp_332 :
    exitExcessOp 332 = some (.PUSH2, some (UInt256.ofNat 408, 2)) := rfl
theorem exitExcessOp_335 : exitExcessOp 335 = some (.JUMPI, none) := rfl
theorem exitExcessOp_408 : exitExcessOp 408 = some (.JUMPDEST, none) := rfl
theorem exitExcessOp_409 :
    exitExcessOp 409 = some (.PUSH32, some (UInt256.ofNat inhibitor, 32)) := rfl
theorem exitExcessOp_442 : exitExcessOp 442 = some (.JUMPDEST, none) := rfl
theorem exitExcessOp_443 : exitExcessOp 443 = some (.PUSH0, none) := rfl
theorem exitExcessOp_444 : exitExcessOp 444 = some (.SSTORE, none) := rfl
theorem exitExcessOp_445 : exitExcessOp 445 = some (.PUSH0, none) := rfl
theorem exitExcessOp_446 :
    exitExcessOp 446 = some (.PUSH1, some (UInt256.ofNat 1, 1)) := rfl
theorem exitExcessOp_448 : exitExcessOp 448 = some (.SSTORE, none) := rfl
theorem exitExcessOp_449 :
    exitExcessOp 449 = some (.PUSH1, some (UInt256.ofNat 68, 1)) := rfl
theorem exitExcessOp_451 : exitExcessOp 451 = some (.MUL, none) := rfl
theorem exitExcessOp_452 : exitExcessOp 452 = some (.PUSH0, none) := rfl
theorem exitExcessOp_453 : exitExcessOp 453 = some (.RETURN, none) := rfl

theorem depositHeadOp_471 : depositHeadOp 471 = some (.JUMPDEST, none) := rfl
theorem depositHeadOp_472 : depositHeadOp 472 = some (.SWAP2, none) := rfl
theorem depositHeadOp_473 : depositHeadOp 473 = some (.ADD, none) := rfl
theorem depositHeadOp_474 : depositHeadOp 474 = some (.DUP1, none) := rfl
theorem depositHeadOp_475 : depositHeadOp 475 = some (.SWAP3, none) := rfl
theorem depositHeadOp_476 : depositHeadOp 476 = some (.EQ, none) := rfl
theorem depositHeadOp_477 :
    depositHeadOp 477 = some (.PUSH2, some (UInt256.ofNat 489, 2)) := rfl
theorem depositHeadOp_480 : depositHeadOp 480 = some (.JUMPI, none) := rfl
theorem depositHeadOp_484 : depositHeadOp 484 = some (.SSTORE, none) := rfl
theorem depositHeadOp_489 : depositHeadOp 489 = some (.JUMPDEST, none) := rfl
theorem depositHeadOp_490 : depositHeadOp 490 = some (.SWAP1, none) := rfl
theorem depositHeadOp_491 : depositHeadOp 491 = some (.POP, none) := rfl
theorem depositHeadOp_492 : depositHeadOp 492 = some (.PUSH0, none) := rfl
theorem depositHeadOp_493 :
    depositHeadOp 493 = some (.PUSH1, some (UInt256.ofNat 2, 1)) := rfl
theorem depositHeadOp_495 : depositHeadOp 495 = some (.SSTORE, none) := rfl
theorem depositHeadOp_496 : depositHeadOp 496 = some (.PUSH0, none) := rfl
theorem depositHeadOp_497 :
    depositHeadOp 497 = some (.PUSH1, some (UInt256.ofNat 3, 1)) := rfl
theorem depositHeadOp_499 : depositHeadOp 499 = some (.SSTORE, none) := rfl

/-! Tiny hex pins (do not `fromHex` the whole runtime). -/

theorem deposit_excess_open_bytes :
    opcodeAt (fromHex "5b3661024257") 0 = some (.JUMPDEST, none) ∧
    opcodeAt (fromHex "5b3661024257") 1 = some (.CALLDATASIZE, none) ∧
    opcodeAt (fromHex "5b3661024257") 2 =
      some (.PUSH2, some (UInt256.ofNat Deposit.set_inhibitor, 2)) ∧
    opcodeAt (fromHex "5b3661024257") 5 = some (.JUMPI, none) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem exit_excess_open_bytes :
    opcodeAt (fromHex "5b3661019857") 0 = some (.JUMPDEST, none) ∧
    opcodeAt (fromHex "5b3661019857") 1 = some (.CALLDATASIZE, none) ∧
    opcodeAt (fromHex "5b3661019857") 2 =
      some (.PUSH2, some (UInt256.ofNat Exit.set_inhibitor, 2)) ∧
    opcodeAt (fromHex "5b3661019857") 5 = some (.JUMPI, none) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem deposit_store_bytes :
    opcodeAt (fromHex "5b5f555f60015560b8025ff3") 0 = some (.JUMPDEST, none) ∧
    opcodeAt (fromHex "5b5f555f60015560b8025ff3") 1 = some (.PUSH0, none) ∧
    opcodeAt (fromHex "5b5f555f60015560b8025ff3") 2 = some (.SSTORE, none) ∧
    opcodeAt (fromHex "5b5f555f60015560b8025ff3") 11 = some (.RETURN, none) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem table_agrees_open_deposit :
    depositExcessOp Deposit.update_excess = some (.JUMPDEST, none) ∧
    depositExcessOp (Deposit.update_excess + 1) = some (.CALLDATASIZE, none) ∧
    depositExcessOp Deposit.set_inhibitor = some (.JUMPDEST, none) ∧
    depositExcessOp Deposit.store_excess = some (.JUMPDEST, none) ∧
    depositExcessOp (Deposit.store_excess + 11) = some (.RETURN, none) :=
  ⟨depositExcessOp_500, depositExcessOp_501, depositExcessOp_578,
    depositExcessOp_612, depositExcessOp_623⟩

/-! ## Generic CFG steps -/

theorem step_JUMPDEST {op : Nat → Option (Operation .EVM × Option (UInt256 × Nat))}
    {jumps : Array UInt256} {m : SysCfg}
    (hop : op m.pc = some (.JUMPDEST, none)) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gjumpdest) :
    cfgStep op jumps m = .ok (sysNext m (m.pc + 1) m.stack (m.gas - Gjumpdest)) := by
  have hg : ¬ m.gas < Gjumpdest := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_CALLDATASIZE {op jumps m}
    (hop : op m.pc = some (.CALLDATASIZE, none)) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gbase) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1)
            ((if m.calldataNonempty then UInt256.ofNat 1 else UInt256.ofNat 0) :: m.stack)
            (m.gas - Gbase)) := by
  have hg : ¬ m.gas < Gbase := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_PUSH0 {op jumps m}
    (hop : op m.pc = some (.PUSH0, none)) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gbase) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (UInt256.ofNat 0 :: m.stack) (m.gas - Gbase)) := by
  have hg : ¬ m.gas < Gbase := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_PUSH1 {op jumps m imm}
    (hop : op m.pc = some (.PUSH1, some (imm, 1))) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1 + 1) (imm :: m.stack) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_PUSH2 {op jumps m imm}
    (hop : op m.pc = some (.PUSH2, some (imm, 2))) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1 + 2) (imm :: m.stack) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_PUSH32 {op jumps m imm}
    (hop : op m.pc = some (.PUSH32, some (imm, 32))) (hhalt : m.halted = false)
    (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1 + 32) (imm :: m.stack) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hg]

theorem step_JUMPI_taken {op jumps m dest cond rest}
    (hop : op m.pc = some (.JUMPI, none)) (hhalt : m.halted = false)
    (hst : m.stack = dest :: cond :: rest) (hgas : m.gas ≥ Ghigh)
    (hcond : (cond != UInt256.ofNat 0) = true)
    (hjd : jumps.contains dest = true) :
    cfgStep op jumps m =
      .ok (sysNext m dest.toNat rest (m.gas - Ghigh)) := by
  have hg : ¬ m.gas < Ghigh := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg, hcond, hjd]

theorem step_JUMPI_fall {op jumps m dest cond rest}
    (hop : op m.pc = some (.JUMPI, none)) (hhalt : m.halted = false)
    (hst : m.stack = dest :: cond :: rest) (hgas : m.gas ≥ Ghigh)
    (hcond : (cond != UInt256.ofNat 0) = false) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) rest (m.gas - Ghigh)) := by
  have hg : ¬ m.gas < Ghigh := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg, hcond]

theorem step_JUMP {op jumps m dest rest}
    (hop : op m.pc = some (.JUMP, none)) (hhalt : m.halted = false)
    (hst : m.stack = dest :: rest) (hgas : m.gas ≥ Gmid)
    (hjd : jumps.contains dest = true) :
    cfgStep op jumps m =
      .ok (sysNext m dest.toNat rest (m.gas - Gmid)) := by
  have hg : ¬ m.gas < Gmid := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg, hjd]

theorem step_SSTORE {op jumps m slot val rest}
    (hop : op m.pc = some (.SSTORE, none)) (hhalt : m.halted = false)
    (hst : m.stack = slot :: val :: rest) (hgas : m.gas ≥ Gsset) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) rest (m.gas - Gsset) (m.storage.insert slot val)) := by
  have hg : ¬ m.gas < Gsset := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_SLOAD {op jumps m slot rest}
    (hop : op m.pc = some (.SLOAD, none)) (hhalt : m.halted = false)
    (hst : m.stack = slot :: rest) (hgas : m.gas ≥ Gcoldsload) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1)
            (m.storage.getD slot (UInt256.ofNat 0) :: rest)
            (m.gas - Gcoldsload)) := by
  have hg : ¬ m.gas < Gcoldsload := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_RETURN {op jumps m off size rest}
    (hop : op m.pc = some (.RETURN, none)) (hhalt : m.halted = false)
    (hst : m.stack = off :: size :: rest) :
    cfgStep op jumps m = .ok (sysHalt m size.toNat) := by
  simp [cfgStep, sysHalt, hhalt, hop, hst]

theorem step_POP {op jumps m x rest}
    (hop : op m.pc = some (.POP, none)) (hhalt : m.halted = false)
    (hst : m.stack = x :: rest) (hgas : m.gas ≥ Gbase) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) rest (m.gas - Gbase)) := by
  have hg : ¬ m.gas < Gbase := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_DUP2 {op jumps m a b rest}
    (hop : op m.pc = some (.DUP2, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (b :: a :: b :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_DUP3 {op jumps m a b c rest}
    (hop : op m.pc = some (.DUP3, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: c :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (c :: a :: b :: c :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_SWAP1 {op jumps m a b rest}
    (hop : op m.pc = some (.SWAP1, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (b :: a :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_SWAP2 {op jumps m a b c rest}
    (hop : op m.pc = some (.SWAP2, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: c :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (c :: b :: a :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_SWAP3 {op jumps m a b c d rest}
    (hop : op m.pc = some (.SWAP3, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: c :: d :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (d :: b :: c :: a :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_ADD {op jumps m a b rest}
    (hop : op m.pc = some (.ADD, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) ((a + b) :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_SUB {op jumps m a b rest}
    (hop : op m.pc = some (.SUB, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) ((a - b) :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_MUL {op jumps m a b rest}
    (hop : op m.pc = some (.MUL, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Glow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) ((a * b) :: rest) (m.gas - Glow)) := by
  have hg : ¬ m.gas < Glow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_EQ {op jumps m a b rest}
    (hop : op m.pc = some (.EQ, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (UInt256.eq a b :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_GT {op jumps m a b rest}
    (hop : op m.pc = some (.GT, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: b :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (UInt256.gt a b :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]

theorem step_DUP1 {op jumps m a rest}
    (hop : op m.pc = some (.DUP1, none)) (hhalt : m.halted = false)
    (hst : m.stack = a :: rest) (hgas : m.gas ≥ Gverylow) :
    cfgStep op jumps m =
      .ok (sysNext m (m.pc + 1) (a :: a :: rest) (m.gas - Gverylow)) := by
  have hg : ¬ m.gas < Gverylow := not_lt_of_ge hgas
  simp [cfgStep, sysNext, hhalt, hop, hst, hg]
set_option linter.unusedVariables false

/-- Gas remaining after a known prefix of the Yellow-paper schedule. -/
theorem store_gas_ok {gas used need : Nat}
    (hgas : gas ≥ sysStoreGas) (hsum : used + need ≤ sysStoreGas) :
    gas - used ≥ need := by
  simp [sysStoreGas] at hgas hsum ⊢
  omega

theorem block_gas_ok {gas used need : Nat}
    (hgas : gas ≥ sysBlockGas) (hsum : used + need ≤ sysBlockGas) :
    gas - used ≥ need := by
  simp [sysBlockGas] at hgas hsum ⊢
  omega

/-- Fresh machine at a ground PC. Avoids `{ m with stack := x :: xs }` (4.31). -/
def mkSys (pc : Nat) (stack : List UInt256) (gas : Nat) (storage : Storage)
    (cd : Bool) : SysCfg :=
  { pc := pc, stack := stack, gas := gas, storage := storage,
    calldataNonempty := cd }

theorem pc_mkSys (pc stack gas storage cd) :
    (mkSys pc stack gas storage cd).pc = pc := rfl

theorem halted_mkSys (pc stack gas storage cd) :
    (mkSys pc stack gas storage cd).halted = false := rfl

/-! ## Named drain / excess image (not `Ξ`)

`applyDrainPointers` / `applySystemStorage` are the control-slot writes
`update_head` / `store_excess` implement. Stale item slots are unconstrained
(F2). `accum_loop` encode is not claimed. -/

theorem nextHead_lt_size {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    nextHead kind σ < UInt256.size := by
  have ht := tail_lt_2_64 wf
  have hhead : queueHead σ < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (head_le_tail wf) ht
  unfold nextHead
  split_ifs
  · exact Nat.lt_trans (by decide : 0 < 2 ^ 64) two_pow_64_lt_size
  · have hcap : capOf kind ≤ 64 := by
      cases kind with
      | deposit => simp [capOf_deposit]
      | exit => simp [capOf_exit]
    have : queueHead σ + capOf kind < 2 ^ 64 + 64 :=
      Nat.add_lt_add_of_lt_of_le hhead hcap
    exact Nat.lt_trans this (by decide : 2 ^ 64 + 64 < UInt256.size)

theorem nextTail_lt_size {kind : Kind} {σ : Storage} (wf : WellFormed kind σ) :
    nextTail kind σ < UInt256.size := by
  have ht := tail_lt_2_64 wf
  unfold nextTail
  split_ifs
  · exact Nat.lt_trans (by decide : 0 < 2 ^ 64) two_pow_64_lt_size
  · exact Nat.lt_trans ht two_pow_64_lt_size

theorem applyDrainPointers_head {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    queueHead (applyDrainPointers kind σ) = nextHead kind σ := by
  unfold applyDrainPointers storeWord queueHead loadNat QUEUE_HEAD QUEUE_TAIL
  rw [loadU256_insert_of_ne]
  · rw [loadU256_insert_self]
    exact toNat_ofNat_of_lt (nextHead_lt_size wf)
  · exact ofNat_slot_ne.2.2.2.2.2.2.2.2.2.2.2

theorem applyDrainPointers_tail {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ) :
    queueTail (applyDrainPointers kind σ) = nextTail kind σ := by
  unfold applyDrainPointers storeWord queueTail loadNat QUEUE_TAIL
  rw [loadU256_insert_self]
  exact toNat_ofNat_of_lt (nextTail_lt_size wf)

/-- Full drain (length ≤ cap) zeroes both pointers. -/
theorem applyDrainPointers_full {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ)
    (h : queueTail σ - queueHead σ ≤ capOf kind) :
    queueHead (applyDrainPointers kind σ) = 0 ∧
      queueTail (applyDrainPointers kind σ) = 0 := by
  constructor
  · rw [applyDrainPointers_head wf, nextHead_full h]
  · rw [applyDrainPointers_tail wf, nextTail_full h]

/-- Partial drain advances HEAD by cap and leaves TAIL unchanged. -/
theorem applyDrainPointers_partial {kind : Kind} {σ : Storage}
    (wf : WellFormed kind σ)
    (h : ¬ queueTail σ - queueHead σ ≤ capOf kind) :
    queueHead (applyDrainPointers kind σ) = queueHead σ + capOf kind ∧
      queueTail (applyDrainPointers kind σ) = queueTail σ := by
  constructor
  · rw [applyDrainPointers_head wf, nextHead_partial h]
  · rw [applyDrainPointers_tail wf, nextTail_partial h]

theorem fifo_of_wellformed {kind : Kind} {σ : Storage} (wf : WellFormed kind σ)
    (hitems : ∀ idx, decodeItem kind (applyDrainPointers kind σ) idx =
      decodeItem kind σ idx) :
    queueOf kind (applyDrainPointers kind σ) =
      (queueOf kind σ).drop (capOf kind) :=
  fifo_matches_model wf (applyDrainPointers_head wf) (applyDrainPointers_tail wf) hitems

theorem applySystemStorage_count (kind : Kind) (σ : Storage) (b : Bool) :
    slotCount (applySystemStorage kind σ b) = 0 := by
  unfold applySystemStorage
  exact slotCount_after_zero _ _

theorem applySystemStorage_excess (kind : Kind) (σ : Storage) (b : Bool) :
    loadU256 (applySystemStorage kind σ b) SLOT_EXCESS =
      UInt256.ofNat (nextExcess (toModel kind σ 0) b) := by
  unfold applySystemStorage
  exact slotExcess_after_store _ _

/-! ## `store_excess` (count := 0, excess stored, RETURN)

Common tail of every system excess branch. Each instruction is a CFG step
at a ground PC; never reverts. Post-storage is `storeWordU` / `storeWord`. -/

theorem deposit_store_excess_ok (σ : Storage) (newExcess drain : UInt256)
    (gas : Nat) (cd : Bool) (hgas : gas ≥ sysStoreGas) :
    ∃ m' : SysCfg,
      m'.halted = true ∧
        slotCount m'.storage = 0 ∧
        loadU256 m'.storage SLOT_EXCESS = newExcess := by
  let m0 := mkSys 612 [newExcess, drain] gas σ cd
  have s0 := step_JUMPDEST (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m0) (hop := hop_of_pc (pc_mkSys 612 _ _ _ _) depositExcessOp_612)
    (hhalt := halted_mkSys 612 _ _ _ _)
    (hgas := by simp [m0, mkSys, Gjumpdest, sysStoreGas] at hgas ⊢; omega)
  let m1 := mkSys 613 [newExcess, drain] (gas - Gjumpdest) σ cd
  have s1 := step_PUSH0 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m1) (hop := hop_of_pc (pc_mkSys 613 _ _ _ _) depositExcessOp_613)
    (hhalt := halted_mkSys 613 _ _ _ _)
    (hgas := by simp [m1, mkSys, Gjumpdest, Gbase, sysStoreGas] at hgas ⊢; omega)
  let m2 := mkSys 614 [UInt256.ofNat 0, newExcess, drain]
    (gas - Gjumpdest - Gbase) σ cd
  have s2 := step_SSTORE (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m2) (slot := UInt256.ofNat 0) (val := newExcess) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 614 _ _ _ _) depositExcessOp_614)
    (hhalt := halted_mkSys 614 _ _ _ _) (hst := rfl)
    (hgas := by simp [m2, mkSys, Gjumpdest, Gbase, Gsset, sysStoreGas] at hgas ⊢; omega)
  let σ1 := σ.insert (UInt256.ofNat 0) newExcess
  let m3 := mkSys 615 [drain] (gas - Gjumpdest - Gbase - Gsset) σ1 cd
  have s3 := step_PUSH0 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m3) (hop := hop_of_pc (pc_mkSys 615 _ _ _ _) depositExcessOp_615)
    (hhalt := halted_mkSys 615 _ _ _ _)
    (hgas := by simp [m3, mkSys, Gjumpdest, Gbase, Gsset, sysStoreGas] at hgas ⊢; omega)
  let m4 := mkSys 616 [UInt256.ofNat 0, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase) σ1 cd
  have s4 := step_PUSH1 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m4) (imm := UInt256.ofNat 1)
    (hop := hop_of_pc (pc_mkSys 616 _ _ _ _) depositExcessOp_616)
    (hhalt := halted_mkSys 616 _ _ _ _)
    (hgas := by
      simp [m4, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let m5 := mkSys 618 [UInt256.ofNat 1, UInt256.ofNat 0, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow) σ1 cd
  have s5 := step_SSTORE (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m5) (slot := UInt256.ofNat 1) (val := UInt256.ofNat 0) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 618 _ _ _ _) depositExcessOp_618)
    (hhalt := halted_mkSys 618 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m5, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let σ2 := σ1.insert (UInt256.ofNat 1) (UInt256.ofNat 0)
  let m6 := mkSys 619 [drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset) σ2 cd
  have s6 := step_PUSH1 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m6) (imm := UInt256.ofNat 184)
    (hop := hop_of_pc (pc_mkSys 619 _ _ _ _) depositExcessOp_619)
    (hhalt := halted_mkSys 619 _ _ _ _)
    (hgas := by
      simp [m6, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let m7 := mkSys 621 [UInt256.ofNat 184, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow) σ2 cd
  have s7 := step_MUL (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m7) (hop := hop_of_pc (pc_mkSys 621 _ _ _ _) depositExcessOp_621)
    (hhalt := halted_mkSys 621 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m7, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, Glow, sysStoreGas] at hgas ⊢
      omega)
  let m8 := mkSys 622 [UInt256.ofNat 184 * drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow - Glow) σ2 cd
  have s8 := step_PUSH0 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m8) (hop := hop_of_pc (pc_mkSys 622 _ _ _ _) depositExcessOp_622)
    (hhalt := halted_mkSys 622 _ _ _ _)
    (hgas := by
      simp [m8, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, Glow, sysStoreGas] at hgas ⊢
      omega)
  let m9 := mkSys 623 [UInt256.ofNat 0, UInt256.ofNat 184 * drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow - Glow - Gbase)
    σ2 cd
  have s9 := step_RETURN (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m9) (off := UInt256.ofNat 0) (size := UInt256.ofNat 184 * drain) (rest := [])
    (hop := hop_of_pc (pc_mkSys 623 _ _ _ _) depositExcessOp_623)
    (hhalt := halted_mkSys 623 _ _ _ _) (hst := rfl)
  refine ⟨sysHalt m9 (UInt256.ofNat 184 * drain).toNat, rfl, ?cnt, ?exc⟩
  · simpa [sysHalt, m9, mkSys, σ2, σ1, storeWord, storeWordU, SLOT_EXCESS, SLOT_COUNT]
      using slotCount_after_zero σ newExcess
  · simpa [sysHalt, m9, mkSys, σ2, σ1, storeWord, storeWordU, SLOT_EXCESS, SLOT_COUNT]
      using slotExcess_after_store σ newExcess

/-- Nonempty system calldata at `update_excess` stores `INHIBITOR` and zeroes
count. CFG-level; never reverts. Matches `systemCall` (success, count 0,
nonempty excess). -/
theorem deposit_update_excess_nonempty (σ : Storage) (drain : UInt256)
    (gas : Nat) (hgas : gas ≥ sysBlockGas) :
    ∃ m' : SysCfg,
      m'.halted = true ∧
        slotCount m'.storage = 0 ∧
        loadU256 m'.storage SLOT_EXCESS = UInt256.ofNat inhibitor := by
  let m0 := mkSys 500 [drain] gas σ true
  have s0 := step_JUMPDEST (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m0) (hop := hop_of_pc (pc_mkSys 500 _ _ _ _) depositExcessOp_500)
    (hhalt := halted_mkSys 500 _ _ _ _)
    (hgas := by simp [m0, mkSys, Gjumpdest, sysBlockGas] at hgas ⊢; omega)
  let m1 := mkSys 501 [drain] (gas - Gjumpdest) σ true
  have s1 := step_CALLDATASIZE (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m1) (hop := hop_of_pc (pc_mkSys 501 _ _ _ _) depositExcessOp_501)
    (hhalt := halted_mkSys 501 _ _ _ _)
    (hgas := by simp [m1, mkSys, Gjumpdest, Gbase, sysBlockGas] at hgas ⊢; omega)
  let m2 := mkSys 502 [UInt256.ofNat 1, drain] (gas - Gjumpdest - Gbase) σ true
  have s2 := step_PUSH2 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m2) (imm := UInt256.ofNat 578)
    (hop := hop_of_pc (pc_mkSys 502 _ _ _ _) depositExcessOp_502)
    (hhalt := halted_mkSys 502 _ _ _ _)
    (hgas := by
      simp [m2, mkSys, Gjumpdest, Gbase, Gverylow, sysBlockGas] at hgas ⊢; omega)
  let m3 := mkSys 505 [UInt256.ofNat 578, UInt256.ofNat 1, drain]
    (gas - Gjumpdest - Gbase - Gverylow) σ true
  have s3 := step_JUMPI_taken (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m3) (dest := UInt256.ofNat 578) (cond := UInt256.ofNat 1) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 505 _ _ _ _) depositExcessOp_505)
    (hhalt := halted_mkSys 505 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m3, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
    (hcond := bne_one_zero')
    (hjd := deposit_system_jumpdests.1)
  let m4 := mkSys 578 [drain]
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh) σ true
  have s4 := step_JUMPDEST (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m4) (hop := hop_of_pc (pc_mkSys 578 _ _ _ _) depositExcessOp_578)
    (hhalt := halted_mkSys 578 _ _ _ _)
    (hgas := by
      simp [m4, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
  let m5 := mkSys 579 [drain]
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest) σ true
  have s5 := step_PUSH32 (op := depositExcessOp) (jumps := depositJumpdests)
    (m := m5) (imm := UInt256.ofNat inhibitor)
    (hop := hop_of_pc (pc_mkSys 579 _ _ _ _) depositExcessOp_579)
    (hhalt := halted_mkSys 579 _ _ _ _)
    (hgas := by
      simp [m5, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
  have hrem :
      gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow ≥ sysStoreGas := by
    simp [Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas, sysStoreGas] at hgas ⊢
    omega
  exact deposit_store_excess_ok σ (UInt256.ofNat inhibitor) drain
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow) true hrem

/-- Empty calldata: the `update_excess` `JUMPI` falls through (not to
`set_inhibitor`). The fold itself is `nextExcess_eq_asm`. -/
theorem deposit_update_excess_empty_jumpi_fall (σ : Storage) (drain : UInt256)
    (gas : Nat) (hgas : gas ≥ sysBlockGas) :
    cfgStep depositExcessOp depositJumpdests
      (mkSys 505 [UInt256.ofNat 578, UInt256.ofNat 0, drain] gas σ false) =
    .ok (sysNext (mkSys 505 [UInt256.ofNat 578, UInt256.ofNat 0, drain] gas σ false)
          506 [drain] (gas - Ghigh) σ) := by
  have h := step_JUMPI_fall (op := depositExcessOp) (jumps := depositJumpdests)
    (m := mkSys 505 [UInt256.ofNat 578, UInt256.ofNat 0, drain] gas σ false)
    (dest := UInt256.ofNat 578) (cond := UInt256.ofNat 0) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 505 _ _ _ _) depositExcessOp_505)
    (hhalt := halted_mkSys 505 _ _ _ _) (hst := rfl)
    (hgas := by simp [mkSys, Ghigh, sysBlockGas] at hgas ⊢; omega)
    (hcond := bne_zero_zero')
  simpa [sysNext, mkSys] using h

theorem exit_store_excess_ok (σ : Storage) (newExcess drain : UInt256)
    (gas : Nat) (cd : Bool) (hgas : gas ≥ sysStoreGas) :
    ∃ m' : SysCfg,
      m'.halted = true ∧
        slotCount m'.storage = 0 ∧
        loadU256 m'.storage SLOT_EXCESS = newExcess := by
  let m0 := mkSys 442 [newExcess, drain] gas σ cd
  have s0 := step_JUMPDEST (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m0) (hop := hop_of_pc (pc_mkSys 442 _ _ _ _) exitExcessOp_442)
    (hhalt := halted_mkSys 442 _ _ _ _)
    (hgas := by simp [m0, mkSys, Gjumpdest, sysStoreGas] at hgas ⊢; omega)
  let m1 := mkSys 443 [newExcess, drain] (gas - Gjumpdest) σ cd
  have s1 := step_PUSH0 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m1) (hop := hop_of_pc (pc_mkSys 443 _ _ _ _) exitExcessOp_443)
    (hhalt := halted_mkSys 443 _ _ _ _)
    (hgas := by simp [m1, mkSys, Gjumpdest, Gbase, sysStoreGas] at hgas ⊢; omega)
  let m2 := mkSys 444 [UInt256.ofNat 0, newExcess, drain]
    (gas - Gjumpdest - Gbase) σ cd
  have s2 := step_SSTORE (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m2) (slot := UInt256.ofNat 0) (val := newExcess) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 444 _ _ _ _) exitExcessOp_444)
    (hhalt := halted_mkSys 444 _ _ _ _) (hst := rfl)
    (hgas := by simp [m2, mkSys, Gjumpdest, Gbase, Gsset, sysStoreGas] at hgas ⊢; omega)
  let σ1 := σ.insert (UInt256.ofNat 0) newExcess
  let m3 := mkSys 445 [drain] (gas - Gjumpdest - Gbase - Gsset) σ1 cd
  have s3 := step_PUSH0 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m3) (hop := hop_of_pc (pc_mkSys 445 _ _ _ _) exitExcessOp_445)
    (hhalt := halted_mkSys 445 _ _ _ _)
    (hgas := by simp [m3, mkSys, Gjumpdest, Gbase, Gsset, sysStoreGas] at hgas ⊢; omega)
  let m4 := mkSys 446 [UInt256.ofNat 0, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase) σ1 cd
  have s4 := step_PUSH1 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m4) (imm := UInt256.ofNat 1)
    (hop := hop_of_pc (pc_mkSys 446 _ _ _ _) exitExcessOp_446)
    (hhalt := halted_mkSys 446 _ _ _ _)
    (hgas := by
      simp [m4, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let m5 := mkSys 448 [UInt256.ofNat 1, UInt256.ofNat 0, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow) σ1 cd
  have s5 := step_SSTORE (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m5) (slot := UInt256.ofNat 1) (val := UInt256.ofNat 0) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 448 _ _ _ _) exitExcessOp_448)
    (hhalt := halted_mkSys 448 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m5, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let σ2 := σ1.insert (UInt256.ofNat 1) (UInt256.ofNat 0)
  let m6 := mkSys 449 [drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset) σ2 cd
  have s6 := step_PUSH1 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m6) (imm := UInt256.ofNat 68)
    (hop := hop_of_pc (pc_mkSys 449 _ _ _ _) exitExcessOp_449)
    (hhalt := halted_mkSys 449 _ _ _ _)
    (hgas := by
      simp [m6, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, sysStoreGas] at hgas ⊢; omega)
  let m7 := mkSys 451 [UInt256.ofNat 68, drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow) σ2 cd
  have s7 := step_MUL (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m7) (hop := hop_of_pc (pc_mkSys 451 _ _ _ _) exitExcessOp_451)
    (hhalt := halted_mkSys 451 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m7, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, Glow, sysStoreGas] at hgas ⊢
      omega)
  let m8 := mkSys 452 [UInt256.ofNat 68 * drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow - Glow) σ2 cd
  have s8 := step_PUSH0 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m8) (hop := hop_of_pc (pc_mkSys 452 _ _ _ _) exitExcessOp_452)
    (hhalt := halted_mkSys 452 _ _ _ _)
    (hgas := by
      simp [m8, mkSys, Gjumpdest, Gbase, Gsset, Gverylow, Glow, sysStoreGas] at hgas ⊢
      omega)
  let m9 := mkSys 453 [UInt256.ofNat 0, UInt256.ofNat 68 * drain]
    (gas - Gjumpdest - Gbase - Gsset - Gbase - Gverylow - Gsset - Gverylow - Glow - Gbase)
    σ2 cd
  have s9 := step_RETURN (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m9) (off := UInt256.ofNat 0) (size := UInt256.ofNat 68 * drain) (rest := [])
    (hop := hop_of_pc (pc_mkSys 453 _ _ _ _) exitExcessOp_453)
    (hhalt := halted_mkSys 453 _ _ _ _) (hst := rfl)
  refine ⟨sysHalt m9 (UInt256.ofNat 68 * drain).toNat, rfl, ?cnt, ?exc⟩
  · simpa [sysHalt, m9, mkSys, σ2, σ1, storeWord, storeWordU, SLOT_EXCESS, SLOT_COUNT]
      using slotCount_after_zero σ newExcess
  · simpa [sysHalt, m9, mkSys, σ2, σ1, storeWord, storeWordU, SLOT_EXCESS, SLOT_COUNT]
      using slotExcess_after_store σ newExcess

theorem exit_update_excess_nonempty (σ : Storage) (drain : UInt256)
    (gas : Nat) (hgas : gas ≥ sysBlockGas) :
    ∃ m' : SysCfg,
      m'.halted = true ∧
        slotCount m'.storage = 0 ∧
        loadU256 m'.storage SLOT_EXCESS = UInt256.ofNat inhibitor := by
  let m0 := mkSys 330 [drain] gas σ true
  have s0 := step_JUMPDEST (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m0) (hop := hop_of_pc (pc_mkSys 330 _ _ _ _) exitExcessOp_330)
    (hhalt := halted_mkSys 330 _ _ _ _)
    (hgas := by simp [m0, mkSys, Gjumpdest, sysBlockGas] at hgas ⊢; omega)
  let m1 := mkSys 331 [drain] (gas - Gjumpdest) σ true
  have s1 := step_CALLDATASIZE (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m1) (hop := hop_of_pc (pc_mkSys 331 _ _ _ _) exitExcessOp_331)
    (hhalt := halted_mkSys 331 _ _ _ _)
    (hgas := by simp [m1, mkSys, Gjumpdest, Gbase, sysBlockGas] at hgas ⊢; omega)
  let m2 := mkSys 332 [UInt256.ofNat 1, drain] (gas - Gjumpdest - Gbase) σ true
  have s2 := step_PUSH2 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m2) (imm := UInt256.ofNat 408)
    (hop := hop_of_pc (pc_mkSys 332 _ _ _ _) exitExcessOp_332)
    (hhalt := halted_mkSys 332 _ _ _ _)
    (hgas := by
      simp [m2, mkSys, Gjumpdest, Gbase, Gverylow, sysBlockGas] at hgas ⊢; omega)
  let m3 := mkSys 335 [UInt256.ofNat 408, UInt256.ofNat 1, drain]
    (gas - Gjumpdest - Gbase - Gverylow) σ true
  have s3 := step_JUMPI_taken (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m3) (dest := UInt256.ofNat 408) (cond := UInt256.ofNat 1) (rest := [drain])
    (hop := hop_of_pc (pc_mkSys 335 _ _ _ _) exitExcessOp_335)
    (hhalt := halted_mkSys 335 _ _ _ _) (hst := rfl)
    (hgas := by
      simp [m3, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
    (hcond := bne_one_zero')
    (hjd := exit_system_jumpdests.1)
  let m4 := mkSys 408 [drain]
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh) σ true
  have s4 := step_JUMPDEST (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m4) (hop := hop_of_pc (pc_mkSys 408 _ _ _ _) exitExcessOp_408)
    (hhalt := halted_mkSys 408 _ _ _ _)
    (hgas := by
      simp [m4, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
  let m5 := mkSys 409 [drain]
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest) σ true
  have s5 := step_PUSH32 (op := exitExcessOp) (jumps := exitJumpdests)
    (m := m5) (imm := UInt256.ofNat inhibitor)
    (hop := hop_of_pc (pc_mkSys 409 _ _ _ _) exitExcessOp_409)
    (hhalt := halted_mkSys 409 _ _ _ _)
    (hgas := by
      simp [m5, mkSys, Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas] at hgas ⊢; omega)
  have hrem :
      gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow ≥ sysStoreGas := by
    simp [Gjumpdest, Gbase, Gverylow, Ghigh, sysBlockGas, sysStoreGas] at hgas ⊢
    omega
  exact exit_store_excess_ok σ (UInt256.ofNat inhibitor) drain
    (gas - Gjumpdest - Gbase - Gverylow - Ghigh - Gjumpdest - Gverylow) true hrem

/-! ## Pointer SSTOREs (named FIFO; not `Ξ` / `accum_loop`)

`update_head` / `reset_queue` write only slots 2–3. Full drain zeroes both;
partial drain stores `HEAD := head + cap`. These hops are the CFG facts
claim workers need; the logical queue is `fifo_matches_model`. -/

theorem deposit_sstore_head (σ : Storage) (val : UInt256) (rest : List UInt256)
    (gas : Nat) (cd : Bool) (hgas : gas ≥ Gsset) :
    cfgStep depositHeadOp depositJumpdests
      (mkSys 495 (UInt256.ofNat 2 :: val :: rest) gas σ cd) =
    .ok (sysNext (mkSys 495 (UInt256.ofNat 2 :: val :: rest) gas σ cd)
          496 rest (gas - Gsset) (σ.insert (UInt256.ofNat 2) val)) := by
  exact step_SSTORE (op := depositHeadOp) (jumps := depositJumpdests)
    (m := mkSys 495 (UInt256.ofNat 2 :: val :: rest) gas σ cd)
    (slot := UInt256.ofNat 2) (val := val) (rest := rest)
    (hop := hop_of_pc (pc_mkSys 495 _ _ _ _) depositHeadOp_495)
    (hhalt := halted_mkSys 495 _ _ _ _) (hst := rfl) hgas

theorem deposit_sstore_tail (σ : Storage) (val : UInt256) (rest : List UInt256)
    (gas : Nat) (cd : Bool) (hgas : gas ≥ Gsset) :
    cfgStep depositHeadOp depositJumpdests
      (mkSys 499 (UInt256.ofNat 3 :: val :: rest) gas σ cd) =
    .ok (sysNext (mkSys 499 (UInt256.ofNat 3 :: val :: rest) gas σ cd)
          500 rest (gas - Gsset) (σ.insert (UInt256.ofNat 3) val)) := by
  exact step_SSTORE (op := depositHeadOp) (jumps := depositJumpdests)
    (m := mkSys 499 (UInt256.ofNat 3 :: val :: rest) gas σ cd)
    (slot := UInt256.ofNat 3) (val := val) (rest := rest)
    (hop := hop_of_pc (pc_mkSys 499 _ _ _ _) depositHeadOp_499)
    (hhalt := halted_mkSys 499 _ _ _ _) (hst := rfl) hgas

theorem deposit_sstore_head_partial (σ : Storage) (val : UInt256)
    (rest : List UInt256) (gas : Nat) (cd : Bool) (hgas : gas ≥ Gsset) :
    cfgStep depositHeadOp depositJumpdests
      (mkSys 484 (UInt256.ofNat 2 :: val :: rest) gas σ cd) =
    .ok (sysNext (mkSys 484 (UInt256.ofNat 2 :: val :: rest) gas σ cd)
          485 rest (gas - Gsset) (σ.insert (UInt256.ofNat 2) val)) := by
  exact step_SSTORE (op := depositHeadOp) (jumps := depositJumpdests)
    (m := mkSys 484 (UInt256.ofNat 2 :: val :: rest) gas σ cd)
    (slot := UInt256.ofNat 2) (val := val) (rest := rest)
    (hop := hop_of_pc (pc_mkSys 484 _ _ _ _) depositHeadOp_484)
    (hhalt := halted_mkSys 484 _ _ _ _) (hst := rfl) hgas

/-- Control-slot image of a full drain: HEAD and TAIL are 0. -/
theorem reset_queue_storage (σ : Storage) :
    queueHead ((σ.insert (UInt256.ofNat 2) (UInt256.ofNat 0)).insert
      (UInt256.ofNat 3) (UInt256.ofNat 0)) = 0 ∧
    queueTail ((σ.insert (UInt256.ofNat 2) (UInt256.ofNat 0)).insert
      (UInt256.ofNat 3) (UInt256.ofNat 0)) = 0 := by
  constructor
  · unfold queueHead loadNat loadU256 QUEUE_HEAD
    rw [Std.TreeMap.getD_insert]
    split_ifs with hcmp
    · exact absurd (Std.LawfulEqOrd.eq_of_compare hcmp) ofNat_slot_ne.2.2.2.2.2.2.2.2.2.2.2
    · rw [Std.TreeMap.getD_insert_self]
      exact toNat_ofNat_of_lt (by decide)
  · unfold queueTail loadNat loadU256 QUEUE_TAIL
    rw [Std.TreeMap.getD_insert_self]
    exact toNat_ofNat_of_lt (by decide)


/-! ## Correspondence summary

Closed under `WellFormed`, `isSystemCaller`, `gas ≥ 30_000_000`, explicit
CFG fuel (`sysBlockGas` / `sysStoreGas`):

* Gate (F3): system iff `read_requests`; user iff userPc.
* `systemCall` success: `store_excess` / nonempty `update_excess` halt via
  `RETURN`; the modelled system blocks never `REVERT`.
* `SLOT_COUNT := 0` after `store_excess` (deposit and exit CFG).
* Excess: nonempty calldata → `INHIBITOR` (deposit and exit CFG). Empty
  calldata: the `update_excess` `JUMPI` falls (deposit). The fold
  (`inhibited → 0`, else `max(0, excess+count-target)` with assembly `GT`,
  on-target both `0`) is `nextExcess_eq_asm`.
* FIFO: `nextHead` / `nextTail` / `applyDrainPointers_*` / `fifo_matches_model`
  match `Model.systemCall`'s `queue.drop cap`. Pointer `SSTORE` hops at
  HEAD/TAIL. `accum_loop` encode is not claimed as `Ξ`.
-/

theorem systemCall_count_closed (s : Model.State) (b : Bool) :
    (systemCall s b).state.count = 0 := by
  unfold systemCall; simp

theorem systemCall_success_closed (s : Model.State) (b : Bool) :
    (systemCall s b).isRevert = false := by
  unfold systemCall; simp

theorem systemCall_excess_nonempty_closed (s : Model.State) :
    (systemCall s true).state.storedExcess = inhibitor := by
  unfold systemCall nextExcess; simp

theorem systemCall_fifo_closed (s : Model.State) (b : Bool) :
    (systemCall s b).state.queue = s.queue.drop (capOf s.kind) := by
  unfold systemCall; simp

end Eip8282.Audit.Correspondence


