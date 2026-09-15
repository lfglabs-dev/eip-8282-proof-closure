import Eip8282.Audit.Execution.Deposit
import Eip8282.Audit.EntryReach.Path

/-!
# Entry reachability of the builder-deposits runtime

Every complete `Ξ` message call into the pinned `builder_deposits` runtime is
followed here from the entry machine to the halting instruction it reaches,
along every path the code has: the eight user endpoints and the system drain.
Each theorem is a chain of the generated block lemmas
(`Eip8282.Audit.EntryReach.Blocks`) and the step lemmas
(`Eip8282.Audit.EntryReach.Steps`), so it rests on `SymExec.pureStep_sound`,
the kernel-checked decodes of the pinned image, and EVMYulLean's own `Z` and
`EvmYul.step` — no trace, no `native_decide`, no premise about the model.

The branch conditions are the words the code tests, read off the entry state by
`Eip8282.Audit.EntryReach.Machine`'s readers; relating them to `Model.userCall`
is the next slice (OPERANDS), not this one.
-/

namespace Eip8282.Audit.EntryReach.Deposit

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach

set_option maxRecDepth 100000

variable (c : XiCall .deposit)









theorem executionEnv_st₂ : (st₂ c).executionEnv = c.env := rfl



/-! ## The opening gate -/



/-! ## The user path up to the fee loop -/






/-! ## The fee loop

`fake_expo` runs `[out, acc, i, X, 17] ↦ [acc + out, X·acc / (i·17), 1 + i, X, 17]`
until `acc = 0`; `feeExit` (in `Path`) is that recurrence on words. -/







/-! ## The user path onto the dispatch -/






/-! ## The `revert:` subroutine -/

/-- Entering `revert:` (`pc = 624`) with any stack: three instructions later the
machine stands on the `REVERT` with two zero operands pushed, and that `REVERT`
halts publishing the empty slice. -/
theorem revert_tail {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (r : Stack UInt256) (haw : aw.toNat = 0)
    (hg : 5 ≤ g.toNat) (hr : r.length + 3 ≤ 1024) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 5 ≤ g'.toNat ∧
      Reaches depositJumpdests 3 (at_ c st mem aw g 624 r e)
        (at_ c st mem aw g' 627 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e') ∧
      Halt depositJumpdests (at_ c st mem aw g' 627 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e')
        .REVERT (mem.readWithPadding 0 0) := by
  obtain ⟨g', e', hg', hr'⟩ := block_step hvj_deposit deposit_b624 deposit_b624_ok (n := 3)
    deposit_b624_bound rfl (deposit_b624_shape c st mem aw g e r) (hcode_of_env c henv) rfl hg
    (by simpa using hr)
  refine ⟨g', e', hg', hr', ?_⟩
  exact halt_REVERT deposit_s627 (hcode_of_env c henv) (B := 0) (by gas_omega) (by decide) (by decide)
    rfl (Nat.zero_le _) (by gas_omega)

/-! ## The user endpoints

Each theorem names the branch words that select the endpoint, and delivers the
completed path: the halting machine, its opcode, and the bytes it publishes.
`mem₀`/`aw₀` are the entry memory (empty) and active-word count (zero). -/






/-- **Inhibited.** `SLOT_EXCESS = INHIBITOR`: the user path reverts at once. -/
theorem user_inhibited (huser : callerWord c ≠ sysW) (hinh : excessWord c = INH)
    (hg : 2200 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c 15 (at_ c (touch (entrySt c) (UInt256.ofNat 0)) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: excessWord c :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s26 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b27 deposit_b27_ok (n := 6) deposit_b27_bound rfl
      (deposit_b27_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s67 (hcode_of_env c rfl)
      ((eq_ne_zero_iff _ _).mpr hinh.symm) (hvj_deposit 624 (by decide)) (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := touch (entrySt c) (UInt256.ofNat 0))
    (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄) rfl [excessWord c] (activeWords_entry c)
    (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by decide), hhalt⟩

/-- **Bad calldata size.** Uninhibited, `|I_d| ∉ {0, 184}`: revert after the fee
quote. -/
theorem user_badsize_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hne184 : cdsizeWord c ≠ UInt256.ofNat 184) (hne0 : cdsizeWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s142 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hne184 h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b143 deposit_b143_ok (n := 2) deposit_b143_bound rfl
      (deposit_b143_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s147 (hcode_of_env c rfl) hne0 (hvj_deposit 624 (by decide))
      (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄)
    rfl [feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩

/-- **Paid getter.** Empty calldata with nonzero value: revert. -/
theorem user_paidGetter_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s142 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => by rw [hsize] at h; exact absurd h (by decide)))
      (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b143 deposit_b143_ok (n := 2) deposit_b143_bound rfl
      (deposit_b143_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s147 (hcode_of_env c rfl) hsize (by gas_omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b148 deposit_b148_ok (n := 2) deposit_b148_bound rfl
      (deposit_b148_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h4
  simp only [valueW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s152 (hcode_of_env c rfl) hval (hvj_deposit 624 (by decide))
      (by gas_omega) (by simp)
  clear h5
  obtain ⟨g₆, e₆, hg₆, hr₆⟩ := h6
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₆) (e := e₆)
    rfl [feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₆.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩



/-- **Underpaid submission.** 184-byte calldata with `Iᵥ < fee`: revert. -/
theorem user_underpay_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hlt : valueWord c < feeWord o')
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s166 (hcode_of_env c rfl) ((lt_ne_zero_iff _ _).mpr hlt)
      (hvj_deposit 624 (by decide)) (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄)
    rfl [feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩



/-- **Amount below the floor.** Paid 184-byte calldata whose amount is under one
gwei's worth: revert. -/
theorem user_amountFloor_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : amountWord c < UInt256.ofNat 1000000000)
    (hg : 87 * n + 4600 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 90) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: amountWord c :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s166 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by gas_omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b167 deposit_b167_ok (n := 8) deposit_b167_bound rfl
      (deposit_b167_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h4
  simp only [cdW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s190 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hfloor)
      (hvj_deposit 624 (by decide)) (by gas_omega) (by simp)
  clear h5
  obtain ⟨g₆, e₆, hg₆, hr₆⟩ := h6
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₆) (e := e₆)
    rfl [amountWord c, feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₆.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩

/-- **Stake not covered.** The value left after the fee is below the amount in
wei: revert. -/
theorem user_stake_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : ¬ amountWord c < UInt256.ofNat 1000000000)
    (hstake : (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c)
    (hg : 87 * n + 4600 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 100) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 627
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s142 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_deposit 159 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b159 deposit_b159_ok (n := 5) deposit_b159_bound rfl
      (deposit_b159_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s166 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by gas_omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b167 deposit_b167_ok (n := 8) deposit_b167_bound rfl
      (deposit_b167_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h4
  simp only [cdW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s190 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hfloor)
      (by gas_omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b191 deposit_b191_ok (n := 7) deposit_b191_bound rfl
      (deposit_b191_shape c (st₂ c) _ _ g₁ e₁ (amountWord c) (feeWord o') [])
      (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h6
  simp only [valueW_touch] at h7
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s204 (hcode_of_env c rfl) ((lt_ne_zero_iff _ _).mpr hstake)
      (hvj_deposit 624 (by decide)) (by gas_omega) (by simp)
  clear h7
  obtain ⟨g₈, e₈, hg₈, hr₈⟩ := h8
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c) (g := g₈) (e := e₈)
    rfl [] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₈.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩


/-! ## The accepted deposit

The write path: eight `SSTORE`s, the `CALLDATACOPY` that stages the record, its
`LOG0`, and `STOP`. The pieces of the final state are named so the theorem can be
read: `countStore` is the state after `SLOT_COUNT` is bumped, `tailWord` the
`QUEUE_TAIL` it then reads, `slotBase` the base slot of the appended item, and
`dw off` the calldata word at `off`. -/















/-! ## The system path

`read_requests` reads the queue pointers, clamps the count at `MAX_PER_BLOCK`,
runs `accum_loop` once per drained item, updates the pointers, folds the excess
and returns the staged records. -/










/-! ### One iteration of `accum_loop` -/





















/-! ### The loop -/





/-! ### `update_head` and `update_excess` -/









/-! ### The system endpoint -/







end Eip8282.Audit.EntryReach.Deposit
