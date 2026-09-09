import Eip8282.Audit.Integrator.SuccessInversion
import Eip8282.Audit.Integrator.SubmissionCall

/-!
# Necessary admission checks from actual successful executions

This module follows actual successful execution through the fee-loop exit and
input checks. No sufficient-gas or fee-completion premise is supplied. The word
calldata-size checks are kept explicit; exact natural lengths need the separate
calldata-size fit condition because CALLDATASIZE is a word conversion.
-/
namespace Eip8282.Audit.Integrator.AdmissionInversion

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec Eip8282.Audit.EntryReach
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall)
open SuccessInversion

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

/-- Recover both the completed recurrence and its actual exit continuation. -/
theorem deposit_fee_exit (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests
      (at_ c st mem aw g 100 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter rest gas count,
      feeExit numerator n o a i = some (output,counter) ∧
      X rest depositJumpdests (at_ c st mem aw gas 127
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) = .ok (.success final out) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        have hcode := Deposit.hcode_of_env c henv
        obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock deposit_b100 deposit_b100_ok hcode rfl
          (deposit_b100_shape c st mem aw g e o ⟨0⟩ [i,numerator,UInt256.ofNat 17]) h
        rw [withGE_at] at hx1
        obtain ⟨f2, cost, _, _, hx2⟩ := success_jumpi_taken
          (decodeAt_of_code_pc hcode rfl deposit_s107) rfl ((feeLoop_exit_iff _).mpr rfl) hx1
        rw [jumpi_taken_at, withGE_at] at hx2
        exact ⟨0, o, i, f2, _, _, by simp [feeExit], hx2⟩
      · obtain ⟨rest, gas, count, hf, hnext⟩ := deposit_fee_cycle c henv ha h
        obtain ⟨n, output, counter, remaining, gas', count', hloop, htail⟩ :=
          ih rest (by omega) hnext
        exact ⟨n+1, output, counter, remaining, gas', count',
          by simpa only [feeExit, if_neg ha] using hloop, htail⟩

/-- The actual rejection subroutine cannot have a successful continuation. -/
theorem deposit_revert_impossible (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests (at_ c st mem aw g 624 stk e) = .ok (.success final out)) :
    False := by
  have hcode := Deposit.hcode_of_env c henv
  obtain ⟨rest, gas, count, _, hx⟩ := success_symBlock deposit_b624 deposit_b624_ok hcode rfl
    (deposit_b624_shape c st mem aw g e stk) h
  rw [withGE_at] at hx
  apply success_not_revert hx
  exact congrArg Prod.fst (decodeAt_of_code_pc
    (st := at_ c st mem aw gas 627 [UInt256.ofNat 0, UInt256.ofNat 0] count) hcode rfl deposit_s627)

/-- A successful JUMPI to the rejection block must fall through. -/
theorem deposit_guard (c : XiCall .deposit)
    {fuel pc : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {cond : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (hop : opcodeAt depositRuntime pc = some (.JUMPI, none))
    (h : X fuel depositJumpdests
      (at_ c st mem aw g pc (UInt256.ofNat 624 :: cond :: stk) e) = .ok (.success final out)) :
    cond = ⟨0⟩ ∧ ∃ rest gas count,
      X rest depositJumpdests (at_ c st mem aw gas (pc+1) stk count) = .ok (.success final out) := by
  have hd := decodeAt_of_code_pc
    (st := at_ c st mem aw g pc (UInt256.ofNat 624 :: cond :: stk) e)
    (Deposit.hcode_of_env c henv) rfl hop
  have hc : cond = ⟨0⟩ := by
    by_contra hn
    obtain ⟨rest, cost, _, _, hx⟩ := success_jumpi_taken hd rfl hn h
    rw [jumpi_taken_at, withGE_at] at hx
    exact deposit_revert_impossible c henv hx
  obtain ⟨rest, cost, _, _, hx⟩ := success_jumpi_untaken hd rfl hc h
  rw [jumpi_fallthrough_at, withGE_at] at hx
  exact ⟨hc, rest, _, _, hx⟩

/-- Recover both the completed recurrence and its actual exit continuation. -/
theorem exit_fee_exit (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o a i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests
      (at_ c st mem aw g 99 [o,a,i,numerator,UInt256.ofNat 17] e) =
        .ok (.success final out)) :
    ∃ n output counter rest gas count,
      feeExit numerator n o a i = some (output,counter) ∧
      X rest exitJumpdests (at_ c st mem aw gas 126
        [output,⟨0⟩,counter,numerator,UInt256.ofNat 17] count) = .ok (.success final out) := by
  induction fuel using Nat.strong_induction_on generalizing o a i g e with
  | h fuel ih =>
      by_cases ha : a = ⟨0⟩
      · subst a
        have hcode := Exit.hcode_of_env c henv
        obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock exit_b99 exit_b99_ok hcode rfl
          (exit_b99_shape c st mem aw g e o ⟨0⟩ [i,numerator,UInt256.ofNat 17]) h
        rw [withGE_at] at hx1
        obtain ⟨f2, cost, _, _, hx2⟩ := success_jumpi_taken
          (decodeAt_of_code_pc hcode rfl exit_s106) rfl ((feeLoop_exit_iff _).mpr rfl) hx1
        rw [jumpi_taken_at, withGE_at] at hx2
        exact ⟨0, o, i, f2, _, _, by simp [feeExit], hx2⟩
      · obtain ⟨rest, gas, count, hf, hnext⟩ := exit_fee_cycle c henv ha h
        obtain ⟨n, output, counter, remaining, gas', count', hloop, htail⟩ :=
          ih rest (by omega) hnext
        exact ⟨n+1, output, counter, remaining, gas', count',
          by simpa only [feeExit, if_neg ha] using hloop, htail⟩

/-- The actual rejection subroutine cannot have a successful continuation. -/
theorem exit_revert_impossible (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests (at_ c st mem aw g 454 stk e) = .ok (.success final out)) :
    False := by
  have hcode := Exit.hcode_of_env c henv
  obtain ⟨rest, gas, count, _, hx⟩ := success_symBlock exit_b454 exit_b454_ok hcode rfl
    (exit_b454_shape c st mem aw g e stk) h
  rw [withGE_at] at hx
  apply success_not_revert hx
  exact congrArg Prod.fst (decodeAt_of_code_pc
    (st := at_ c st mem aw gas 457 [UInt256.ofNat 0, UInt256.ofNat 0] count) hcode rfl exit_s457)

/-- A successful JUMPI to the rejection block must fall through. -/
theorem exit_guard (c : XiCall .exit)
    {fuel pc : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {cond : UInt256} {stk : Stack UInt256} {final : EVM.State} {out : ByteArray}
    (henv : st.executionEnv = c.env)
    (hop : opcodeAt exitRuntime pc = some (.JUMPI, none))
    (h : X fuel exitJumpdests
      (at_ c st mem aw g pc (UInt256.ofNat 454 :: cond :: stk) e) = .ok (.success final out)) :
    cond = ⟨0⟩ ∧ ∃ rest gas count,
      X rest exitJumpdests (at_ c st mem aw gas (pc+1) stk count) = .ok (.success final out) := by
  have hd := decodeAt_of_code_pc
    (st := at_ c st mem aw g pc (UInt256.ofNat 454 :: cond :: stk) e)
    (Exit.hcode_of_env c henv) rfl hop
  have hc : cond = ⟨0⟩ := by
    by_contra hn
    obtain ⟨rest, cost, _, _, hx⟩ := success_jumpi_taken hd rfl hn h
    rw [jumpi_taken_at, withGE_at] at hx
    exact exit_revert_impossible c henv hx
  obtain ⟨rest, cost, _, _, hx⟩ := success_jumpi_untaken hd rfl hc h
  rw [jumpi_fallthrough_at, withGE_at] at hx
  exact ⟨hc, rest, _, _, hx⟩

/-- Invert a nonhalting supported instruction, retaining actual memory charge.
Its pure shape may update memory, storage or logs; Z contributes only gas. -/
theorem success_effect {fuel : Nat} {vj : Array UInt256}
    {pre shaped final : EVM.State} {out : ByteArray} {op : Operation .EVM}
    {arg : Option (UInt256 × Nat)} (hm : op ∈ allOps) (hn : Halting op = false)
    (hd : decodeAt pre = (op,arg)) (hstep : EvmYul.step op arg pre = .ok shaped)
    (h : X fuel vj pre = .ok (.success final out)) :
    ∃ rest gas count, X rest vj (withGE shaped gas count) = .ok (.success final out) := by
  obtain ⟨rest, cost, mid, post, _, hz, hs, _, htail⟩ := success_continue hd hn h
  cases rest with
  | zero => simp only [X_zero] at htail; contradiction
  | succ rest =>
      have hmid : mid = withGE pre mid.gasAvailable pre.execLength := by
        rw [Z_ok_state hz]
        rfl
      have he : post = withGE shaped (mid.gasAvailable - UInt256.ofNat cost) (pre.execLength+1) := by
        change EvmYul.EVM.step (rest+1) cost (some (op,arg)) mid = .ok post at hs
        rw [EVM_step_eq_step hm, stepPre_eq_withGE, hmid, withGE_withGE,
          step_withGE hm, hstep] at hs
        exact (Except.ok.inj hs).symm
      exact ⟨rest+1, _, _, he ▸ htail⟩

/-- Actual successful RETURN publishes exactly the bytes selected by its stack. -/
theorem success_return_bytes {fuel : Nat} {vj : Array UInt256}
    {pre final : EVM.State} {out : ByteArray} {off len : UInt256} {stk : Stack UInt256}
    (hd : decodeAt pre = (.RETURN,none)) (hst : pre.stack = off :: len :: stk)
    (h : X fuel vj pre = .ok (.success final out)) :
    out = pre.memory.readWithPadding off.toNat len.toNat := by
  obtain ⟨rest, cost, op, arg, mid, post, _, hd', hz, hs, hcase⟩ := success_step h
  have hop := hd.symm.trans hd'
  cases hop
  cases rest with
  | zero => change Except.error ExecutionException.OutOfFuel = Except.ok post at hs; cases hs
  | succ rest =>
      have hmidstack : mid.stack = off :: len :: stk := (Z_ok_stack hz).trans hst
      change EvmYul.EVM.step (rest+1) cost (some (.RETURN,none)) mid = .ok post at hs
      rw [EVM_step_eq_step (by decide : Operation.RETURN ∈ allOps), stepPre_eq_withGE,
        step_withGE (by decide : Operation.RETURN ∈ allOps), step_RETURN hmidstack] at hs
      have he := (Except.ok.inj hs).symm
      rcases hcase with ⟨hn, _⟩ | ⟨hout, _, _⟩
      · have hn' := H_eq_none_iff.mp hn
        simp at hn'
      · rw [he] at hout
        change some (mid.memory.readWithPadding off.toNat len.toNat) = some out at hout
        rw [Z_ok_memory hz] at hout
        exact (Option.some.inj hout).symm

/-- Exact byte encoding, independent of memory contents before MSTORE. -/
theorem getter_bytes (memory : ByteArray) (price : UInt256) :
    (mstoreMem memory (UInt256.ofNat 0) price).readWithPadding 0 32 = price.toByteArray := by
  unfold mstoreMem
  change (ByteArray.write price.toByteArray 0 memory 0 32).readWithPadding 0 32 = _
  rw [ByteArray.readWithPadding_write_self_of_pad _ _ _ _ (by norm_num) (by norm_num)
    (UInt256.size_toByteArray price) (by simp)]

/-- The actual successful getter suffix returns the stack's price word. -/
theorem deposit_getter_suffix (c : XiCall .deposit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {price : UInt256} {final : EVM.State} {out : ByteArray} (henv : st.executionEnv = c.env)
    (h : X fuel depositJumpdests (at_ c st mem aw g 153 [price] e) = .ok (.success final out)) :
    out = price.toByteArray := by
  have hcode := Deposit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock deposit_b153 deposit_b153_ok hcode rfl
    (deposit_b153_shape c st mem aw g e [price]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := success_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc hcode rfl deposit_s154) (step_MSTORE rfl) hx1
  change X f2 depositJumpdests
    (at_ c st (mstoreMem mem (UInt256.ofNat 0) price) (mAfter aw 0 32) g2 155 [] e2) =
      .ok (.success final out) at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b155 deposit_b155_ok
    (by exact hcode) rfl (deposit_b155_shape c _ _ _ _ _ [])
  rw [withGE_at] at hx3
  have hb := success_return_bytes
    (decodeAt_of_code_pc (st := at_ c st _ _ g3 158 _ e3) hcode rfl deposit_s158) rfl hx3
  exact hb.trans (getter_bytes mem price)

/-- The actual successful getter suffix returns the stack's price word. -/
theorem exit_getter_suffix (c : XiCall .exit)
    {fuel : Nat} {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {price : UInt256} {final : EVM.State} {out : ByteArray} (henv : st.executionEnv = c.env)
    (h : X fuel exitJumpdests (at_ c st mem aw g 152 [price] e) = .ok (.success final out)) :
    out = price.toByteArray := by
  have hcode := Exit.hcode_of_env c henv
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock exit_b152 exit_b152_ok hcode rfl
    (exit_b152_shape c st mem aw g e [price]) h
  rw [withGE_at] at hx1
  obtain ⟨f2, g2, e2, hx2⟩ := success_effect (by decide : Operation.MSTORE ∈ allOps) (by decide)
    (decodeAt_of_code_pc hcode rfl exit_s153) (step_MSTORE rfl) hx1
  change X f2 exitJumpdests
    (at_ c st (mstoreMem mem (UInt256.ofNat 0) price) (mAfter aw 0 32) g2 154 [] e2) =
      .ok (.success final out) at hx2
  obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b154 exit_b154_ok
    (by exact hcode) rfl (exit_b154_shape c _ _ _ _ _ [])
  rw [withGE_at] at hx3
  have hb := success_return_bytes
    (decodeAt_of_code_pc (st := at_ c st _ _ g3 157 _ e3) hcode rfl exit_s157) rfl hx3
  exact hb.trans (getter_bytes mem price)

/-- Independent operational admission predicate; no desired post-state. -/
def DepositChecks (c : XiCall .deposit) (price : UInt256) (out : ByteArray) : Prop :=
  (Deposit.cdsizeWord c = ⟨0⟩ ∧ Deposit.valueWord c = ⟨0⟩ ∧ out = price.toByteArray) ∨
  (Deposit.cdsizeWord c = UInt256.ofNat 184 ∧ ¬ Deposit.valueWord c < price ∧
    ¬ Deposit.amountWord c < UInt256.ofNat 1000000000 ∧
    ¬ (Deposit.valueWord c-price) < UInt256.ofNat 1000000000 * Deposit.amountWord c)

def ExitChecks (c : XiCall .exit) (price : UInt256) (out : ByteArray) : Prop :=
  (Exit.cdsizeWord c = ⟨0⟩ ∧ Exit.valueWord c = ⟨0⟩ ∧ out = price.toByteArray) ∨
  (Exit.cdsizeWord c = UInt256.ofNat 48 ∧ ¬ Exit.valueWord c < price)

/-- Success after the fee exit forces all admission checks of the selected path. -/
theorem deposit_after_fee (c : XiCall .deposit)
    {fuel : Nat} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (h : X fuel depositJumpdests (at_ c (Deposit.st₂ c) mem aw g 127
      [o,⟨0⟩,i,numerator,UInt256.ofNat 17] e) = .ok (.success final out)) :
    DepositChecks c (o / UInt256.ofNat 17) out := by
  have hcode := Deposit.hcode_of_env c (st := Deposit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) deposit_b127 deposit_b127_ok
    (by exact hcode) rfl (deposit_b127_shape c (Deposit.st₂ c) mem aw g e o ⟨0⟩ i numerator
      (UInt256.ofNat 17) [])
  rw [withGE_at] at hx1
  by_cases hs : Deposit.cdsizeWord c = UInt256.ofNat 184
  · obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc
        (st := at_ c (Deposit.st₂ c) mem aw g1 142 _ e1) (by exact hcode) rfl deposit_s142)
      rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b159 deposit_b159_ok
      (by exact hcode) rfl (deposit_b159_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx3
    obtain ⟨hpaid, f4, g4, e4, hx4⟩ := deposit_guard c rfl deposit_s166 hx3
    obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b167 deposit_b167_ok
      (by exact hcode) rfl (deposit_b167_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx5
    obtain ⟨hfloor, f6, g6, e6, hx6⟩ := deposit_guard c rfl deposit_s190 hx5
    obtain ⟨f7, g7, e7, _, hx7⟩ := success_symBlock (h := hx6) deposit_b191 deposit_b191_ok
      (by exact hcode) rfl (deposit_b191_shape c _ _ _ _ _ _ _ _)
    rw [withGE_at] at hx7
    obtain ⟨hstake, _, _, _, _⟩ := deposit_guard c rfl deposit_s204 hx7
    exact Or.inr ⟨hs, (lt_eq_zero_iff _ _).mp hpaid,
      (gt_eq_zero_iff _ _).mp hfloor, (lt_eq_zero_iff _ _).mp hstake⟩
  · obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc
        (st := at_ c (Deposit.st₂ c) mem aw g1 142 _ e1) (by exact hcode) rfl deposit_s142)
      rfl ((eq_eq_zero_iff _ _).mpr (fun he => hs he.symm)) hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) deposit_b143 deposit_b143_ok
      (by exact hcode) rfl (deposit_b143_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx3
    obtain ⟨hsize, f4, g4, e4, hx4⟩ := deposit_guard c rfl deposit_s147 hx3
    obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) deposit_b148 deposit_b148_ok
      (by exact hcode) rfl (deposit_b148_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx5
    obtain ⟨hvalue, _, _, _, hx6⟩ := deposit_guard c rfl deposit_s152 hx5
    exact Or.inl ⟨hsize, hvalue, deposit_getter_suffix c rfl hx6⟩

/-- Success after the fee exit forces all admission checks of the selected path. -/
theorem exit_after_fee (c : XiCall .exit)
    {fuel : Nat} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    {o i numerator : UInt256} {final : EVM.State} {out : ByteArray}
    (h : X fuel exitJumpdests (at_ c (Exit.st₂ c) mem aw g 126
      [o,⟨0⟩,i,numerator,UInt256.ofNat 17] e) = .ok (.success final out)) :
    ExitChecks c (o / UInt256.ofNat 17) out := by
  have hcode := Exit.hcode_of_env c (st := Exit.st₂ c) rfl
  obtain ⟨f1, g1, e1, _, hx1⟩ := success_symBlock (h := h) exit_b126 exit_b126_ok
    (by exact hcode) rfl (exit_b126_shape c (Exit.st₂ c) mem aw g e o ⟨0⟩ i numerator
      (UInt256.ofNat 17) [])
  rw [withGE_at] at hx1
  by_cases hs : Exit.cdsizeWord c = UInt256.ofNat 48
  · obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_taken
      (decodeAt_of_code_pc
        (st := at_ c (Exit.st₂ c) mem aw g1 141 _ e1) (by exact hcode) rfl exit_s141)
      rfl ((eq_ne_zero_iff _ _).mpr hs.symm) hx1
    rw [jumpi_taken_at, withGE_at] at hx2
    obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b158 exit_b158_ok
      (by exact hcode) rfl (exit_b158_shape c _ _ _ _ _ _ _)
    rw [withGE_at] at hx3
    obtain ⟨hpaid, _, _, _, _⟩ := exit_guard c rfl exit_s164 hx3
    exact Or.inr ⟨hs, (lt_eq_zero_iff _ _).mp hpaid⟩
  · obtain ⟨f2, cost2, _, _, hx2⟩ := success_jumpi_untaken
      (decodeAt_of_code_pc
        (st := at_ c (Exit.st₂ c) mem aw g1 141 _ e1) (by exact hcode) rfl exit_s141)
      rfl ((eq_eq_zero_iff _ _).mpr (fun he => hs he.symm)) hx1
    rw [jumpi_fallthrough_at, withGE_at] at hx2
    obtain ⟨f3, g3, e3, _, hx3⟩ := success_symBlock (h := hx2) exit_b142 exit_b142_ok
      (by exact hcode) rfl (exit_b142_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx3
    obtain ⟨hsize, f4, g4, e4, hx4⟩ := exit_guard c rfl exit_s146 hx3
    obtain ⟨f5, g5, e5, _, hx5⟩ := success_symBlock (h := hx4) exit_b147 exit_b147_ok
      (by exact hcode) rfl (exit_b147_shape c _ _ _ _ _ _)
    rw [withGE_at] at hx5
    obtain ⟨hvalue, _, _, _, hx6⟩ := exit_guard c rfl exit_s151 hx5
    exact Or.inl ⟨hsize, hvalue, exit_getter_suffix c rfl hx6⟩

/-- Complete word-admission necessity for an actual successful user Ξ call. -/
theorem deposit_user_success (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    Deposit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Deposit.effExcess c) n = some price ∧ DepositChecks c price out := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Deposit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨hen, _, _, _, hhead⟩ := deposit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, _, _, _, hloop, htail⟩ := deposit_fee_exit c rfl hhead
  exact ⟨hen, n, output / UInt256.ofNat 17,
    quoteWithin_some_of_feeExit hloop, deposit_after_fee c htail⟩

/-- Complete word-admission necessity for an actual successful user Ξ call. -/
theorem exit_user_success (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (h : c.result = .ok (.success published out)) :
    Exit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Exit.effExcess c) n = some price ∧ ExitChecks c price out := by
  obtain ⟨final, _, hx⟩ := xi_success_X c h
  have hu : Exit.callerWord c ≠ sysW := by
    intro he
    exact huser ((callerW_eq_sysW_iff c).mp he)
  obtain ⟨hen, _, _, _, hhead⟩ := exit_user_to_fee_head c hu hx
  obtain ⟨n, output, counter, _, _, _, hloop, htail⟩ := exit_fee_exit c rfl hhead
  exact ⟨hen, n, output / UInt256.ofNat 17,
    quoteWithin_some_of_feeExit hloop, exit_after_fee c htail⟩

/-- Natural input format and payment; the getter includes actual returned bytes. -/
def DepositInputs (c : XiCall .deposit) (price : UInt256) (out : ByteArray) : Prop :=
  (c.env.calldata.size = 0 ∧ c.env.weiValue = ⟨0⟩ ∧ out = price.toByteArray) ∨
  (c.env.calldata.size = 184 ∧ 1000000000 ≤ SubmissionCall.amount c.env.calldata ∧
    price.toNat + 1000000000 * SubmissionCall.amount c.env.calldata ≤ c.env.weiValue.toNat)

def ExitInputs (c : XiCall .exit) (price : UInt256) (out : ByteArray) : Prop :=
  (c.env.calldata.size = 0 ∧ c.env.weiValue = ⟨0⟩ ∧ out = price.toByteArray) ∨
  (c.env.calldata.size = 48 ∧ price.toNat ≤ c.env.weiValue.toNat)

/-- Exact natural calldata lengths need only the stated size-conversion fit.
The uint64 amount itself proves the stake product does not wrap. -/
theorem deposit_inputs_of_checks (c : XiCall .deposit) (price : UInt256) (out : ByteArray)
    (hfit : c.env.calldata.size < UInt256.size) (h : DepositChecks c price out) :
    DepositInputs c price out := by
  rcases h with ⟨hs, hv, ho⟩ | ⟨hs, hp, ha, hstake⟩
  · exact Or.inl ⟨(cdsizeW_eq_zero_iff c hfit).mp hs, hv, ho⟩
  · have hsize := (cdsizeW_eq_ofNat_iff c hfit 184 (by decide)).mp hs
    obtain ⟨hfloor, hpaid⟩ := (SubmissionCall.deposit_checks c price hsize).mp ⟨hp,ha,hstake⟩
    exact Or.inr ⟨hsize, hfloor, hpaid⟩

theorem exit_inputs_of_checks (c : XiCall .exit) (price : UInt256) (out : ByteArray)
    (hfit : c.env.calldata.size < UInt256.size) (h : ExitChecks c price out) :
    ExitInputs c price out := by
  rcases h with ⟨hs, hv, ho⟩ | ⟨hs, hp⟩
  · exact Or.inl ⟨(cdsizeW_eq_zero_iff c hfit).mp hs, hv, ho⟩
  · have hsize := (cdsizeW_eq_ofNat_iff c hfit 48 (by decide)).mp hs
    exact Or.inr ⟨hsize, Nat.le_of_not_gt hp⟩

/-- Natural-format necessity of actual success. Calldata-size fit is a local
representation condition, not an assumed execution or protocol invariant. -/
theorem deposit_user_success_inputs (c : XiCall .deposit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hfit : c.env.calldata.size < UInt256.size)
    (h : c.result = .ok (.success published out)) :
    Deposit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Deposit.effExcess c) n = some price ∧ DepositInputs c price out := by
  obtain ⟨hen, n, price, hq, hc⟩ := deposit_user_success c huser h
  exact ⟨hen, n, price, hq, deposit_inputs_of_checks c price out hfit hc⟩

theorem exit_user_success_inputs (c : XiCall .exit)
    {published : Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate}
    {out : ByteArray} (huser : c.env.source ≠ Eip8282.Audit.EvmRunner.sysAddr)
    (hfit : c.env.calldata.size < UInt256.size)
    (h : c.result = .ok (.success published out)) :
    Exit.excessWord c ≠ INH ∧ ∃ n price,
      quoteWithin (Exit.effExcess c) n = some price ∧ ExitInputs c price out := by
  obtain ⟨hen, n, price, hq, hc⟩ := exit_user_success c huser h
  exact ⟨hen, n, price, hq, exit_inputs_of_checks c price out hfit hc⟩

#print axioms deposit_user_success_inputs
#print axioms exit_user_success_inputs
#print axioms success_effect
#print axioms success_return_bytes
#print axioms deposit_getter_suffix
#print axioms exit_getter_suffix
#print axioms deposit_fee_exit
#print axioms exit_fee_exit
#print axioms deposit_guard
#print axioms exit_guard
#print axioms deposit_user_success
#print axioms exit_user_success

end Eip8282.Audit.Integrator.AdmissionInversion
