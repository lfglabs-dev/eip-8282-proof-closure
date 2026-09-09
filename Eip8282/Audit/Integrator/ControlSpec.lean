import Eip8282.Audit.EntryReach.Words
import Eip8282.Audit.EntryReach.Deposit
import Eip8282.Audit.EntryReach.Exit

/-!
# Independent word-level control specification

These are specifications and arithmetic/operand bridges, not complete-call
P-CONTROL-1 proofs. In particular they assert neither protocol reachability nor
gas sufficiency, storage commitment, initialization, or fee-loop termination.
They do not use the legacy truncated mathematical tariff.

The SYSTEM fold wraps the addition *before* comparison and subtraction. The
fee numerator subtracts the target from the count *before* adding the excess.
Those operations require different bounds for agreement with natural numbers.
-/

namespace Eip8282.Audit.Integrator.ControlSpec

open EvmYul
open Eip8282.Audit.EntryReach
open Eip8282.Audit.XiTransport (XiCall)

inductive CallerPath where
  | user
  | system
  deriving DecidableEq

/-- Only CALLER selects the path. No value, calldata, or storage input occurs. -/
def dispatch (caller : UInt256) : CallerPath :=
  if caller = sysW then .system else .user

theorem dispatch_system_iff (caller : UInt256) :
    dispatch caller = .system ↔ caller = sysW := by
  by_cases h : caller = sysW <;> simp [dispatch, h]

theorem dispatch_user_iff (caller : UInt256) :
    dispatch caller = .user ↔ caller ≠ sysW := by
  by_cases h : caller = sysW <;> simp [dispatch, h]

/-- Environment operand bridge; execution of the dispatcher is proved elsewhere. -/
theorem dispatch_entry_system_iff {kind : Eip8282.Audit.Model.Kind} (c : XiCall kind) :
    dispatch (callerW (entrySt c)) = .system ↔ c.env.source = Eip8282.Audit.EvmRunner.sysAddr := by
  rw [dispatch_system_iff, callerW_eq_sysW_iff]

/-- The fee loop's input, before any fee iteration. -/
def feeInput (target excess count : UInt256) : UInt256 :=
  if target.toNat < count.toNat then (count - target) + excess else excess

/-- Natural-number specification of the fee numerator. -/
def feeInputNat (target excess count : Nat) : Nat := excess + (count - target)

/-- Exact wrapped addition followed by a strict comparison and safe subtraction. -/
def foldWord (target excess count : UInt256) : UInt256 :=
  if target < count + excess then count + excess - target else UInt256.ofNat 0

/-- The mathematical fold uses saturated natural subtraction. -/
def foldNat (target excess count : Nat) : Nat := excess + count - target

/-- Latch, unlock, or fold, with precisely the precedence of the pinned code. -/
def systemExcess (target excess count calldataSize : UInt256) : UInt256 :=
  if calldataSize ≠ ⟨0⟩ then INH
  else if excess = INH then UInt256.ofNat 0
  else foldWord target excess count

theorem systemExcess_latch (target excess count calldataSize : UInt256)
    (h : calldataSize ≠ ⟨0⟩) : systemExcess target excess count calldataSize = INH := by
  simp [systemExcess, h]

theorem systemExcess_unlock (target count : UInt256) :
    systemExcess target INH count ⟨0⟩ = UInt256.ofNat 0 := by
  simp [systemExcess]

/-- An unconditional arithmetic description: modulus precedes subtraction. -/
theorem foldWord_toNat (target excess count : UInt256) :
    (foldWord target excess count).toNat =
      (count.toNat + excess.toNat) % UInt256.size - target.toNat := by
  have hs : (count + excess).toNat =
      (count.toNat + excess.toNat) % UInt256.size := rfl
  unfold foldWord
  by_cases h : target < count + excess
  · rw [if_pos h, toNat_sub_of_le _ _ (Nat.le_of_lt h), hs]
  · rw [if_neg h]
    have hle : (count + excess).toNat ≤ target.toNat := Nat.le_of_not_gt h
    rw [hs] at hle
    exact (Nat.sub_eq_zero_of_le hle).symm

/-- It is the intermediate sum, not merely the final result, that must fit. -/
theorem foldWord_eq_nat_of_sum_lt (target excess count : UInt256)
    (h : excess.toNat + count.toNat < UInt256.size) :
    (foldWord target excess count).toNat = foldNat target.toNat excess.toNat count.toNat := by
  rw [foldWord_toNat, Nat.add_comm count.toNat, Nat.mod_eq_of_lt h]
  rfl

/-- This bound is local to the fold and is not asserted to be a reachable-state invariant. -/
theorem systemExcess_eq_nat_of_sum_lt (target excess count calldataSize : UInt256)
    (h : excess.toNat + count.toNat < UInt256.size) :
    (systemExcess target excess count calldataSize).toNat =
      if calldataSize ≠ ⟨0⟩ then INH.toNat
      else if excess = INH then 0
      else foldNat target.toNat excess.toNat count.toNat := by
  unfold systemExcess
  split
  · rfl
  · split
    · rfl
    · exact foldWord_eq_nat_of_sum_lt target excess count h

/-- Exact fee numerator, including the modular addition if it overflows. -/
theorem feeInput_toNat (target excess count : UInt256) :
    (feeInput target excess count).toNat =
      feeInputNat target.toNat excess.toNat count.toNat % UInt256.size := by
  unfold feeInput feeInputNat
  by_cases h : target.toNat < count.toNat
  · rw [if_pos h]
    change ((count - target).toNat + excess.toNat) % UInt256.size = _
    rw [toNat_sub_of_le _ _ (Nat.le_of_lt h), Nat.add_comm]
  · rw [if_neg h, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h), Nat.add_zero,
      Nat.mod_eq_of_lt (toNat_lt_size excess)]

theorem feeInput_eq_nat_of_sum_lt (target excess count : UInt256)
    (h : feeInputNat target.toNat excess.toNat count.toNat < UInt256.size) :
    (feeInput target excess count).toNat = feeInputNat target.toNat excess.toNat count.toNat := by
  rw [feeInput_toNat, Nat.mod_eq_of_lt h]

/-- Above the target the mathematical operands agree; below it they need not. -/
theorem feeInputNat_eq_foldNat_of_target_le (target excess count : Nat)
    (h : target ≤ count) : feeInputNat target excess count = foldNat target excess count := by
  unfold feeInputNat foldNat
  omega

theorem feeInputNat_ne_foldNat_example : feeInputNat 8 10 0 ≠ foldNat 8 10 0 := by
  decide

/-- Operand identities with the proved path modules; not execution claims. -/
theorem deposit_feeInput (c : XiCall .deposit) :
    feeInput (UInt256.ofNat 8) (Deposit.excessWord c) (Deposit.countWord c) =
      Deposit.effExcess c := rfl

theorem exit_feeInput (c : XiCall .exit) :
    feeInput (UInt256.ofNat 2) (Exit.excessWord c) (Exit.countWord c) =
      Exit.effExcess c := rfl

theorem deposit_systemExcess (c : XiCall .deposit) (st : EvmYul.State .EVM) :
    systemExcess (UInt256.ofNat 8) (slotW st (UInt256.ofNat 0))
      (slotW st (UInt256.ofNat 1)) (Deposit.cdsizeWord c) = Deposit.newExcess c st := rfl

theorem exit_systemExcess (c : XiCall .exit) (st : EvmYul.State .EVM) :
    systemExcess (UInt256.ofNat 2) (slotW st (UInt256.ofNat 0))
      (slotW st (UInt256.ofNat 1)) (Exit.cdsizeWord c) = Exit.newExcess c st := rfl

/-- Kernel-checked counterexample: wrapping after subtraction gives the wrong
answer even though the mathematical *final* answer fits in a word. -/
theorem wrap_before_subtract_counterexample :
    (systemExcess (UInt256.ofNat 8) (UInt256.ofNat (UInt256.size - 5))
      (UInt256.ofNat 10) ⟨0⟩).toNat = 0 ∧
    foldNat 8 (UInt256.size - 5) 10 = UInt256.size - 3 ∧
    foldNat 8 (UInt256.size - 5) 10 < UInt256.size ∧
    (foldNat 8 (UInt256.size - 5) 10) % UInt256.size ≠ 0 := by
  decide +kernel

end Eip8282.Audit.Integrator.ControlSpec
