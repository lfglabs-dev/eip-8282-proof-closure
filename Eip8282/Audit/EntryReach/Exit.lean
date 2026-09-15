import Eip8282.Audit.Execution.Exit
import Eip8282.Audit.EntryReach.Path

/-!
# Entry reachability of the builder-exits runtime

The exit runtime is the deposit runtime with a 48-byte request, a three-slot
record, a drain cap of `16` and an excess target of `2`. Every complete `Ξ`
message call into the pinned `builder_exits` image is followed here from the
entry machine to the halting instruction it reaches: the six user endpoints and
the system drain. As for deposits, each theorem is a chain of the generated block
lemmas (`Eip8282.Audit.EntryReach.Blocks`) and the step lemmas
(`Eip8282.Audit.EntryReach.Steps`) — `SymExec.pureStep_sound`, the kernel-checked
decodes of the pinned image, and EVMYulLean's own `Z` and `EvmYul.step`; no trace,
no `native_decide`, no premise about the model.
-/

namespace Eip8282.Audit.EntryReach.Exit

open EvmYul EvmYul.EVM EvmYul.EVM.Proof
open Eip8282.Audit.SymExec
open Eip8282.Audit.Bytecode Eip8282.Audit.Jumpdests
open Eip8282.Audit.XiTransport (XiCall jumpdestsOf)
open Eip8282.Audit.Model (Kind)
open Eip8282.Audit.EntryReach

set_option maxRecDepth 100000

variable (c : XiCall .exit)









theorem executionEnv_st₂ : (st₂ c).executionEnv = c.env := rfl






/-! ## The opening gate -/



/-! ## The user path up to the fee loop -/






/-! ## The fee loop

The same `fake_expo` as the deposit runtime, at `pc = 99`, exiting to `126`. -/







/-! ## The user path onto the dispatch -/






/-! ## The `revert:` subroutine -/

/-- Entering `revert:` (`pc = 454`) with any stack: three instructions later the
machine stands on the `REVERT` with two zero operands pushed, and that `REVERT`
halts publishing the empty slice. -/
theorem revert_tail {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (r : Stack UInt256) (haw : aw.toNat = 0)
    (hg : 5 ≤ g.toNat) (hr : r.length + 3 ≤ 1024) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 5 ≤ g'.toNat ∧
      Reaches exitJumpdests 3 (at_ c st mem aw g 454 r e)
        (at_ c st mem aw g' 457 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e') ∧
      Halt exitJumpdests (at_ c st mem aw g' 457 (UInt256.ofNat 0 :: UInt256.ofNat 0 :: r) e')
        .REVERT (mem.readWithPadding 0 0) := by
  obtain ⟨g', e', hg', hr'⟩ := block_step hvj_exit exit_b454 exit_b454_ok (n := 3)
    exit_b454_bound rfl (exit_b454_shape c st mem aw g e r) (hcode_of_env c henv) rfl hg
    (by simpa using hr)
  refine ⟨g', e', hg', hr', ?_⟩
  exact halt_REVERT exit_s457 (hcode_of_env c henv) (B := 0) (by gas_omega) (by decide) (by decide)
    rfl (Nat.zero_le _) (by gas_omega)

/-! ## The user endpoints -/



/-- **Inhibited.** `SLOT_EXCESS = INHIBITOR`: the user path reverts at once. -/
theorem user_inhibited (huser : callerWord c ≠ sysW) (hinh : excessWord c = INH)
    (hg : 2200 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c 15 (at_ c (touch (entrySt c) (UInt256.ofNat 0)) (mem₀ c) (aw₀ c) g 457
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: excessWord c :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough exit_s25 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b26 exit_b26_ok (n := 6) exit_b26_bound rfl
      (exit_b26_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s66 (hcode_of_env c rfl)
      ((eq_ne_zero_iff _ _).mpr hinh.symm) (hvj_exit 454 (by decide)) (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := touch (entrySt c) (UInt256.ofNat 0))
    (mem := mem₀ c) (aw := aw₀ c) (g := g₄) (e := e₄) rfl [excessWord c] (activeWords_entry c)
    (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by decide), hhalt⟩

/-- **Bad calldata size.** Uninhibited, `|I_d| ∉ {0, 48}`: revert after the fee
quote. -/
theorem user_badsize_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hne48 : cdsizeWord c ≠ UInt256.ofNat 48) (hne0 : cdsizeWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 457
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough exit_s141 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hne48 h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b142 exit_b142_ok (n := 2) exit_b142_bound rfl
      (exit_b142_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s146 (hcode_of_env c rfl) hne0 (hvj_exit 454 (by decide))
      (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c)
    (g := g₄) (e := e₄) rfl [feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩

/-- **Paid getter.** Empty calldata with nonzero value: revert. -/
theorem user_paidGetter_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c ≠ ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 70) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 457
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: feeWord o' :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough exit_s141 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => by rw [hsize] at h; exact absurd h (by decide)))
      (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b142 exit_b142_ok (n := 2) exit_b142_bound rfl
      (exit_b142_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [cdsizeW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough exit_s146 (hcode_of_env c rfl) hsize (by gas_omega) (by simp)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b147 exit_b147_ok (n := 2) exit_b147_bound rfl
      (exit_b147_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h4
  simp only [valueW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s151 (hcode_of_env c rfl) hval (hvj_exit 454 (by decide))
      (by gas_omega) (by simp)
  clear h5
  obtain ⟨g₆, e₆, hg₆, hr₆⟩ := h6
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c)
    (g := g₆) (e := e₆) rfl [feeWord o'] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₆.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩



/-- **Underpaid request.** 48-byte calldata with `Iᵥ < fee`: revert. -/
theorem user_underpay_reverts (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 48) (hlt : valueWord c < feeWord o')
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80) (at_ c (st₂ c) (mem₀ c) (aw₀ c) g 457
        (UInt256.ofNat 0 :: UInt256.ofNat 0 :: []) e) .REVERT
        ((mem₀ c).readWithPadding 0 0) := by
  have h1 := user_prefix c huser hen hfee (by gas_omega)
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s141 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsize.symm)
      (hvj_exit 158 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b158 exit_b158_ok (n := 4) exit_b158_bound rfl
      (exit_b158_shape c (st₂ c) _ _ g₁ e₁ (feeWord o') []) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h2
  simp only [valueW_touch] at h3
  have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s164 (hcode_of_env c rfl) ((lt_ne_zero_iff _ _).mpr hlt)
      (hvj_exit 454 (by decide)) (by gas_omega) (by simp)
  clear h3
  obtain ⟨g₄, e₄, hg₄, hr₄⟩ := h4
  obtain ⟨g', e', _, hr', hhalt⟩ := revert_tail c (st := st₂ c) (mem := mem₀ c) (aw := aw₀ c)
    (g := g₄) (e := e₄) rfl [] (activeWords_entry c) (by gas_omega) (by simp)
  exact ⟨g', e', ReachesLe.mono (hr₄.trans (Reaches.le hr' le_rfl)) (by gas_omega), hhalt⟩


/-! ## The accepted exit request

The write path: five `SSTORE`s, the caller word and the `CALLDATACOPY` that stage
the 68-byte record, its `LOG0`, and `STOP`. -/
















/-! ## The system path

`read_requests` reads the queue pointers, clamps the count at `MAX_PER_BLOCK = 16`,
runs `accum_loop` once per drained item, updates the pointers, folds the excess
and returns the staged records. -/










/-! ### One iteration of `accum_loop` -/
















/-! ### The loop -/





/-! ### `update_head` and `update_excess` -/









/-! ### The system endpoint -/







end Eip8282.Audit.EntryReach.Exit
