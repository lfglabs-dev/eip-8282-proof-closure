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

/-- The words the user path reads off the entry state. -/
abbrev callerWord : UInt256 := callerW (entrySt c)
abbrev excessWord : UInt256 := slotW (entrySt c) (UInt256.ofNat 0)
abbrev countWord : UInt256 := slotW (entrySt c) (UInt256.ofNat 1)
abbrev valueWord : UInt256 := valueW (entrySt c)
abbrev cdsizeWord : UInt256 := cdsizeW (entrySt c)

/-- The state after the user path's two control reads. -/
abbrev st₂ : EvmYul.State .EVM := touch (touch (entrySt c) (UInt256.ofNat 0)) (UInt256.ofNat 1)

theorem executionEnv_st₂ : (st₂ c).executionEnv = c.env := rfl

theorem hcode_of_env {st : EvmYul.State .EVM} (h : st.executionEnv = c.env) :
    st.executionEnv.code = exitRuntime := by
  rw [h]; exact c.code_pinned

abbrev mem₀ : ByteArray := c.entry.memory
abbrev aw₀ : UInt256 := c.entry.activeWords

/-! ## The opening gate -/

/-- `CALLER; PUSH20 SYSTEM_ADDR; EQ; PUSH2 @read_requests` from the entry machine. -/
theorem gate (hg : 11 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
      Reaches exitJumpdests 4 c.entry
        (at_ c (entrySt c) c.entry.memory c.entry.activeWords g 25
          (UInt256.ofNat 225 :: UInt256.eq sysW (callerWord c) :: []) e) := by
  change ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
    Reaches exitJumpdests 4 (at_ c (entrySt c) c.entry.memory c.entry.activeWords c.gas 0 [] 0) _
  exact block_step hvj_exit exit_b0 exit_b0_ok (n := 4) exit_b0_bound rfl
    (exit_b0_shape c (entrySt c) _ _ c.gas 0 []) (hcode_of_env c rfl) rfl hg (by simp)

/-! ## The user path up to the fee loop -/

/-- `bump_excess`: the excess the fee loop is quoted at (target `2`). -/
def effExcess : UInt256 :=
  if 2 < (countWord c).toNat then (countWord c - UInt256.ofNat 2) + excessWord c
  else excessWord c

/-- From the fall-through of the gate (`pc = 26`) to the fee loop head, on an
uninhibited image. -/
theorem to_fee_loop {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (hen : excessWord c ≠ INH) (hg : 4300 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 4300 ≤ g'.toNat ∧
      ReachesLe exitJumpdests 29 (at_ c (entrySt c) mem aw g 26 [] e)
        (at_ c (st₂ c) mem aw g' 99
          (UInt256.ofNat 0 :: (UInt256.ofNat 17 * UInt256.ofNat 1) :: UInt256.ofNat 1 ::
            effExcess c :: UInt256.ofNat 17 :: []) e') := by
  -- 26..65: the inhibitor test
  have h1 := block_step hvj_exit exit_b26 exit_b26_ok (n := 6) exit_b26_bound rfl
    (exit_b26_shape c (entrySt c) mem aw g e []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  -- 66: not taken
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough exit_s66 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hen h.symm)) (by gas_omega) (by simp)
  clear h1
  -- 67..75: the count test
  have h3 := chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_exit exit_b67 exit_b67_ok (n := 6) exit_b67_bound rfl
      (exit_b67_shape c _ mem aw g₁ e₁ [excessWord c]) (hcode_of_env c rfl) rfl
      (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hcnt : 2 < (countWord c).toNat
  · -- bump_excess taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken exit_s76 (hcode_of_env c rfl)
        ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcnt))
        (hvj_exit 81 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_exit exit_b81 exit_b81_ok (n := 5) exit_b81_bound rfl
        (exit_b81_shape c _ mem aw g₁ e₁ (countWord c) (excessWord c) [])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_exit exit_b87 exit_b87_ok (n := 9) exit_b87_bound rfl
        (exit_b87_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by gas_omega)
        (by simp)
    clear h5
    simp only [effExcess, if_pos hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by gas_omega, Reaches.le hr (by decide)⟩
  · -- bump_excess not taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_fallthrough exit_s76 (hcode_of_env c rfl)
        ((gt_eq_zero_iff _ _).mpr (fun h => hcnt ((ofNat_lt_iff (by decide) _).mp h)))
        (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_exit exit_b77 exit_b77_ok (n := 3) exit_b77_bound rfl
        (exit_b77_shape c _ mem aw g₁ e₁ (countWord c) [excessWord c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_exit exit_b87 exit_b87_ok (n := 9) exit_b87_bound rfl
        (exit_b87_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by gas_omega)
        (by simp)
    clear h5
    simp only [effExcess, if_neg hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by gas_omega, Reaches.le hr (by decide)⟩


/-! ## The fee loop

The same `fake_expo` as the deposit runtime, at `pc = 99`, exiting to `126`. -/

/-- One pass of the loop head onto the taken exit branch, at `acc = 0`. -/
theorem fee_head_exit {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o i X : UInt256) (hg : 25 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 25 ≤ g'.toNat ∧
      Reaches exitJumpdests 7
        (at_ c st mem aw g 99 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 126 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_exit exit_b99 exit_b99_ok (n := 6) exit_b99_bound rfl
    (exit_b99_shape c st mem aw g e o ⟨0⟩ [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by gas_omega) (by simp)
  exact chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_taken exit_s106 (hcode_of_env c henv) ((feeLoop_exit_iff _).mpr rfl)
      (hvj_exit 126 (by decide)) (by gas_omega) (by simp)

/-- One full iteration of the loop, at `acc ≠ 0`. -/
theorem fee_iteration {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o a i X : UInt256) (ha : a ≠ ⟨0⟩) (hg : 87 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 87 ≤ g'.toNat ∧
      Reaches exitJumpdests 24
        (at_ c st mem aw g 99 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 99
          ((a + o) :: ((X * a) / (i * UInt256.ofNat 17)) :: (UInt256.ofNat 1 + i) :: X ::
            UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_exit exit_b99 exit_b99_ok (n := 6) exit_b99_bound rfl
    (exit_b99_shape c st mem aw g e o a [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by gas_omega) (by simp)
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough exit_s106 (hcode_of_env c henv) ((feeLoop_continue_iff _).mpr ha)
      (by gas_omega) (by simp)
  clear h1
  exact chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_exit exit_b107 exit_b107_ok (n := 17) exit_b107_bound rfl
      (exit_b107_shape c st mem aw g₁ e₁ o a i X (UInt256.ofNat 17) []) (hcode_of_env c henv) rfl
      (by gas_omega) (by simp)

/-- **The fee loop terminates where `feeExit` says it does.** -/
theorem fee_loop {st : EvmYul.State .EVM} {mem : ByteArray} {aw : UInt256} (X : UInt256)
    (henv : st.executionEnv = c.env) :
    ∀ (n : Nat) (o a i g : UInt256) (e : Nat) (o' i' : UInt256),
      feeExit X n o a i = some (o', i') → 87 * n + 25 ≤ g.toNat →
      ∃ (g' : UInt256) (e' : Nat), g.toNat - (87 * n + 25) ≤ g'.toNat ∧
        ReachesLe exitJumpdests (24 * n + 7)
          (at_ c st mem aw g 99 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
          (at_ c st mem aw g' 126 (o' :: ⟨0⟩ :: i' :: X :: UInt256.ofNat 17 :: []) e') := by
  intro n
  induction n with
  | zero =>
    intro o a i g e o' i' hexit hg
    simp only [feeExit] at hexit
    split at hexit
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hexit
      obtain ⟨rfl, rfl⟩ := hexit
      subst ha
      obtain ⟨g', e', hg', hr⟩ := fee_head_exit c (mem := mem) (aw := aw) (g := g) (e := e) henv o i X
        (by gas_omega)
      exact ⟨g', e', by gas_omega, Reaches.le hr (by gas_omega)⟩
    · exact absurd hexit (by simp)
  | succ n ih =>
    intro o a i g e o' i' hexit hg
    simp only [feeExit] at hexit
    split at hexit
    · rename_i ha
      simp only [Option.some.injEq, Prod.mk.injEq] at hexit
      obtain ⟨rfl, rfl⟩ := hexit
      subst ha
      obtain ⟨g', e', hg', hr⟩ := fee_head_exit c (mem := mem) (aw := aw) (g := g) (e := e) henv o i X
        (by gas_omega)
      exact ⟨g', e', by gas_omega, Reaches.le hr (by gas_omega)⟩
    · rename_i ha
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := fee_iteration c (mem := mem) (aw := aw) (g := g) (e := e) henv
        o a i X ha (by gas_omega)
      obtain ⟨g', e', hg', hr'⟩ := ih (a + o) ((X * a) / (i * UInt256.ofNat 17))
        (UInt256.ofNat 1 + i) g₁ e₁ o' i' hexit (by gas_omega)
      exact ⟨g', e', by gas_omega, (Reaches.le hr₁ le_rfl).trans hr' |>.mono (by gas_omega)⟩

/-! ## The user path onto the dispatch -/

/-- The fee word the getter returns and the write path compares against. -/
abbrev feeWord (o : UInt256) : UInt256 := o / UInt256.ofNat 17

/-- **From the entry machine to the calldata-size dispatch**, for a user caller
on an uninhibited image whose fee loop terminates within `n` iterations. -/
theorem user_prefix (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256}
    (hfee : feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
      (UInt256.ofNat 1) = some (o', i'))
    (hg : 87 * n + 4400 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - (87 * n + 4400) ≤ g.toNat ∧
      ReachesLe exitJumpdests (24 * n + 60) c.entry
        (at_ c (st₂ c) c.entry.memory c.entry.activeWords g 141
          (UInt256.ofNat 158 :: UInt256.eq (UInt256.ofNat 48) (cdsizeWord c) ::
            feeWord o' :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough exit_s25 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => to_fee_loop c hen (by gas_omega)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ =>
    fee_loop c (effExcess c) rfl n _ _ _ g₁ e₁ o' i' hfee (by gas_omega)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b126 exit_b126_ok (n := 13) exit_b126_bound rfl
      (exit_b126_shape c (st₂ c) _ _ g₁ e₁ o' ⟨0⟩ i' (effExcess c) (UInt256.ofNat 17) [])
      (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h4
  simp only [cdsizeW_touch] at h5
  obtain ⟨g, e, hg', hr⟩ := h5
  exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩


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

/-- The fee-loop hypothesis every uninhibited user endpoint carries. -/
abbrev FeeLoopEnds (n : Nat) (o' i' : UInt256) : Prop :=
  feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
    (UInt256.ofNat 1) = some (o', i')

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

/-- **Fee getter.** Empty calldata, zero value: the fee word is stored at memory
`0` and the 32-byte slice is returned. -/
theorem user_getter_returns (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80)
        (at_ c (st₂ c) (mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o'))
          (mAfter (aw₀ c) 0 32) g 157 (UInt256.ofNat 0 :: UInt256.ofNat 32 :: []) e) .RETURN
        ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32) := by
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
    reach_jumpi_fallthrough exit_s151 (hcode_of_env c rfl) hval (by gas_omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b152 exit_b152_ok (n := 1) exit_b152_bound rfl
      (exit_b152_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h6
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_mstore exit_s153 (hcode_of_env c rfl) (B := 1) (by rw [activeWords_entry]; omega)
      (by decide) (by decide) (M := 6) (by decide) (by gas_omega) (by simp)
  clear h7
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b154 exit_b154_ok (n := 2) exit_b154_bound rfl
      (exit_b154_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h8
  obtain ⟨g', e', hg', hr'⟩ := h9
  refine ⟨g', e', ReachesLe.mono hr' (by gas_omega), ?_⟩
  refine halt_RETURN exit_s157 (hcode_of_env c rfl) (B := 1) (M := 3) (g := g') ?_ ?_ ?_ ?_ ?_ ?_
  · exact toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide)
  · decide
  · decide
  · decide
  · gas_omega
  · simp

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

abbrev countStore : EvmYul.State .EVM :=
  (touch (st₂ c) (UInt256.ofNat 1)).sstore (UInt256.ofNat 1) (UInt256.ofNat 1 + countWord c)
abbrev tailWord : UInt256 := slotW (countStore c) (UInt256.ofNat 3)
abbrev slotBase : UInt256 := UInt256.ofNat 4 + (UInt256.ofNat 3 * tailWord c)
abbrev dw (off : Nat) : UInt256 := cdW (entrySt c) (UInt256.ofNat off)
/-- The caller, left-aligned in a word, as `CALLER; PUSH1 96; SHL` forms it. -/
abbrev addrWord : UInt256 := UInt256.shiftLeft (callerWord c) (UInt256.ofNat 96)

/-- The three item words stored, slot by slot: the caller, then the two calldata words. -/
abbrev itemStored : EvmYul.State .EVM :=
  (((touch (countStore c) (UInt256.ofNat 3)).sstore (slotBase c) (callerWord c)).sstore
    (UInt256.ofNat 1 + slotBase c) (dw c 0)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c)) (dw c 32)

/-- Memory after the record is staged: the caller word at `0`, the 48 calldata
bytes at `20`. -/
abbrev stagedMem : ByteArray :=
  cdcopyMem (itemStored c) (mstoreMem (mem₀ c) (UInt256.ofNat 0) (addrWord c))
    (UInt256.ofNat 20) (UInt256.ofNat 0) (UInt256.ofNat 48)

/-- The final state: item stored, receipt logged, `QUEUE_TAIL` advanced. -/
abbrev appendedSt : EvmYul.State .EVM :=
  (logged (itemStored c) ((stagedMem c).readWithPadding 0 68)).sstore (UInt256.ofNat 3)
    (UInt256.ofNat 1 + tailWord c)

/-- **Accepted request.** 48-byte calldata with the fee paid: the record is
stored and logged and the run halts on `STOP`. Write permission is required,
exactly as `Z` demands at the first `SSTORE`. -/
theorem user_append_stops (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    (hperm : c.env.perm = true)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 48) (hpaid : ¬ valueWord c < feeWord o')
    (hg : 87 * n + 150000 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 120)
        (at_ c (appendedSt c) (stagedMem c)
          (mAfter (mAfter (mAfter (aw₀ c) 0 32) 20 48) 0 68) g 224 [] e)
        .STOP .empty := by
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
    reach_jumpi_fallthrough exit_s164 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hpaid)
      (by gas_omega) (by simp)
  clear h3
  -- 165..172: bump the count
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b165 exit_b165_ok (n := 5) exit_b165_bound rfl
      (exit_b165_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h4
  simp only [slotW_touch] at h5
  have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore exit_s173 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h5
  -- 174..185: base slot and the caller
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b174 exit_b174_ok (n := 9) exit_b174_bound rfl
      (exit_b174_shape c (countStore c) _ _ g₁ e₁ []) (hcode_of_env c (by env_simp)) rfl
      (by gas_omega) (by simp)
  clear h6
  simp only [callerW_touch, callerW_sstore] at h7
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore exit_s186 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h7
  -- 187..200: the two calldata words
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b187 exit_b187_ok (n := 5) exit_b187_bound rfl
      (exit_b187_shape c _ _ _ g₁ e₁ (slotBase c) [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h8
  simp only [cdW_touch, cdW_sstore] at h9
  have h10 := chainLe h9 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore exit_s193 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h9
  have h11 := chainLe h10 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b194 exit_b194_ok (n := 5) exit_b194_bound rfl
      (exit_b194_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h10
  simp only [cdW_touch, cdW_sstore] at h11
  have h12 := chainLe h11 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore exit_s201 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h11
  -- 202..217: stage and log the record
  have h13 := chainLe h12 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b202 exit_b202_ok (n := 4) exit_b202_bound rfl
      (exit_b202_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h12
  simp only [callerW_touch, callerW_sstore] at h13
  have h14 := chainLe h13 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_mstore exit_s207 (hcode_of_env c (by env_simp)) (B := 3)
      (by rw [activeWords_entry]; omega) (by decide) (by decide) (M := 12) (by decide)
      (by gas_omega) (by simp)
  clear h13
  have h15 := chainLe h14 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b208 exit_b208_ok (n := 3) exit_b208_bound rfl
      (exit_b208_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h14
  have h16 := chainLe h15 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_calldatacopy exit_s213 (hcode_of_env c (by env_simp)) (B := 3)
      (toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide))
      (by decide) (by decide) (M := 18) (by decide) (by gas_omega) (by simp)
  clear h15
  have h17 := chainLe h16 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b214 exit_b214_ok (n := 2) exit_b214_bound rfl
      (exit_b214_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h16
  have h18 := chainLe h17 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_log0 exit_s217 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (B := 3)
      (toNat_mAfter_le (toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide))
        (by decide) (by decide))
      (by decide) (by decide) (M := 928) (by decide) (by gas_omega) (by simp)
  clear h17
  -- 218..223: advance the tail
  have h19 := chainLe h18 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b218 exit_b218_ok (n := 3) exit_b218_bound rfl
      (exit_b218_shape c _ _ _ g₁ e₁ (tailWord c) []) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h18
  have h20 := chainLe h19 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore exit_s223 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h19
  obtain ⟨g', e', _, hr'⟩ := h20
  refine ⟨g', e', ReachesLe.mono hr' (by gas_omega), ?_⟩
  exact halt_STOP exit_s224 (hcode_of_env c (by env_simp)) (by simp)


/-! ## The system path

`read_requests` reads the queue pointers, clamps the count at `MAX_PER_BLOCK = 16`,
runs `accum_loop` once per drained item, updates the pointers, folds the excess
and returns the staged records. -/

abbrev tailWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 3)
abbrev headWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 2)
/-- `tail - head`, as the `SUB` computes it. -/
abbrev queueLen : UInt256 := tailWord₀ c - headWord₀ c
/-- `min(tail - head, 16)`: the number of items drained. -/
def drainWord : UInt256 :=
  if queueLen c < UInt256.ofNat 16 then queueLen c else UInt256.ofNat 16

/-- The state after the two pointer reads. -/
abbrev stP : EvmYul.State .EVM := touch (touch (entrySt c) (UInt256.ofNat 3)) (UInt256.ofNat 2)

/-- **From the entry machine to the loop head**, for the system caller. -/
theorem system_prefix (hsys : callerWord c = sysW) (hg : 4300 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 4300 ≤ g.toNat ∧
      ReachesLe exitJumpdests 25 c.entry
        (at_ c (stP c) (mem₀ c) (aw₀ c) g 247
          (UInt256.ofNat 0 :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken exit_s25 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsys.symm)
      (hvj_exit 225 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_exit exit_b225 exit_b225_ok (n := 12) exit_b225_bound rfl
      (exit_b225_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hlt : queueLen c < UInt256.ofNat 16
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s241 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hlt)
        (hvj_exit 245 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b245 exit_b245_ok (n := 2) exit_b245_bound rfl
        (exit_b245_shape c (stP c) _ _ g₁ e₁ [queueLen c, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    simp only [drainWord, if_pos hlt]
    obtain ⟨g, e, hg', hr⟩ := h5
    exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s241 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hlt)
        (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b242 exit_b242_ok (n := 2) exit_b242_bound rfl
        (exit_b242_shape c (stP c) _ _ g₁ e₁ (queueLen c) [headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b245 exit_b245_ok (n := 2) exit_b245_bound rfl
        (exit_b245_shape c (stP c) _ _ g₁ e₁ [UInt256.ofNat 16, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h5
    simp only [drainWord, if_neg hlt]
    obtain ⟨g, e, hg', hr⟩ := h6
    exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩

/-! ### One iteration of `accum_loop` -/

/-- **What one `accum_loop` iteration writes.** The caller word of the item at
`base` goes to `off`, the two request words to `off+20` and `off+52`. Stated as
the pinned code computes each operand, so that the body lemma is a unification. -/
def writeItem (st : EvmYul.State .EVM) (mem : ByteArray) (off base : UInt256) : ByteArray :=
  let off20 := UInt256.ofNat 20 + off
  let off52 := UInt256.ofNat 32 + off20
  let m := mstoreMem mem off (UInt256.shiftLeft (slotW st base) (UInt256.ofNat 96))
  let m := mstoreMem m off20 (slotW st (UInt256.ofNat 1 + base))
  mstoreMem m off52 (slotW st (UInt256.ofNat 2 + base))

/-- The offsets of one item, as naturals: with `i ≤ 15` nothing wraps, and the
last byte written is below `1 104`, so the word count stays under `40`. -/
theorem item_offsets {iW : UInt256} (hi : iW.toNat ≤ 15) :
    (UInt256.ofNat 68 * iW).toNat = 68 * iW.toNat ∧
      (UInt256.ofNat 20 + UInt256.ofNat 68 * iW).toNat = 68 * iW.toNat + 20 ∧
      (UInt256.ofNat 32 + (UInt256.ofNat 20 + UInt256.ofNat 68 * iW)).toNat
        = 68 * iW.toNat + 52 := by
  have h0 : (UInt256.ofNat 68 * iW).toNat = 68 * iW.toNat :=
    toNat_ofNat_mul_of_lt 68 iW (by rw [size_eq]; omega)
  have h20 : (UInt256.ofNat 20 + UInt256.ofNat 68 * iW).toNat = 68 * iW.toNat + 20 := by
    rw [toNat_ofNat_add_of_lt 20 _ (by rw [size_eq, h0]; omega), h0]; omega
  have h52 : (UInt256.ofNat 32 + (UInt256.ofNat 20 + UInt256.ofNat 68 * iW)).toNat
      = 68 * iW.toNat + 52 := by
    rw [toNat_ofNat_add_of_lt 32 _ (by rw [size_eq, h20]; omega), h20]; omega
  exact ⟨h0, h20, h52⟩

/-- The base slot of item `i` of a queue whose head is `head`, as the code forms it. -/
abbrev base (iW head : UInt256) : UInt256 := UInt256.ofNat 4 + (UInt256.ofNat 3 * (iW + head))

/-- The three storage reads of one iteration, as touches. -/
abbrev touchItem (st : EvmYul.State .EVM) (b : UInt256) : EvmYul.State .EVM :=
  touch (touch (touch st b) (UInt256.ofNat 1 + b)) (UInt256.ofNat 2 + b)

theorem touched_touchItem {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (b : UInt256) :
    Touched st₀ (touchItem st b) :=
  ((h.touch _).touch _).touch _

theorem writeItem_of_touched {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (mem : ByteArray)
    (off b : UInt256) : writeItem st mem off b = writeItem st₀ mem off b := by
  unfold writeItem
  simp only [slotW_of_touched h]

/-- **One iteration of `accum_loop`**: from the loop head with `i ≠ count`, the
machine returns to the loop head with the counter bumped, item `i` written to
memory, its three slots touched, and the active-word count still under `40`. -/
theorem drain_body {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (iW cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hi : iW.toNat ≤ 15)
    (hne : iW ≠ cnt) (haw : aw.toNat ≤ 40) (hg : 7000 ≤ g.toNat) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 40 ∧ g.toNat - 7000 ≤ g'.toNat ∧
      ReachesLe exitJumpdests 42
        (at_ c st mem aw g 247 (iW :: cnt :: head :: tail :: []) e)
        (at_ c (touchItem st (base iW head))
          (writeItem st mem (UInt256.ofNat 68 * iW) (base iW head)) aw' g' 247
          ((UInt256.ofNat 1 + iW) :: cnt :: head :: tail :: []) e') := by
  obtain ⟨h0, h20, h52⟩ := item_offsets hi
  have hcode : st.executionEnv.code = exitRuntime := hcode_of_env c henv
  -- 247..253 and the untaken exit test
  have h1 : ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 40 ∧ g.toNat - 13 ≤ g'.toNat ∧
      ReachesLe exitJumpdests 5 (at_ c st mem aw g 247 (iW :: cnt :: head :: tail :: []) e)
        (at_ c st mem aw' g' 254
          (UInt256.ofNat 301 :: UInt256.eq iW cnt :: iW :: cnt :: head :: tail :: []) e') :=
    liftAt (block_step hvj_exit exit_b247 exit_b247_ok (n := 5)
      exit_b247_bound rfl (exit_b247_shape c st mem aw g e iW cnt [head, tail]) hcode rfl
      (by gas_omega) (by simp)) haw
  have h2 := chainAt h1 fun aw g₁ e₁ haw hg₁ => liftAt
    (reach_jumpi_fallthrough exit_s254 hcode ((eq_eq_zero_iff _ _).mpr hne) (by gas_omega)
      (by simp))
    haw
  clear h1
  -- 255..273: base slot, the caller word
  have h3 := chainAt h2 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b255 exit_b255_ok (n := 15) exit_b255_bound rfl
      (exit_b255_shape c st mem aw g₁ e₁ iW cnt head [tail]) hcode rfl (by gas_omega) (by simp))
    haw
  clear h2
  have h4 := chainAt h3 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s274 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h0]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h0]; omega) (by decide)
  clear h3
  -- 275..283: first request word
  have h5 := chainAt h4 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b275 exit_b275_ok (n := 7) exit_b275_bound rfl
      (exit_b275_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h4
  simp only [slotW_touch] at h5
  have h6 := chainAt h5 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s284 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h20]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h20]; omega) (by decide)
  clear h5
  -- 285..293: second request word
  have h7 := chainAt h6 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b285 exit_b285_ok (n := 7) exit_b285_bound rfl
      (exit_b285_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h6
  simp only [slotW_touch] at h7
  have h8 := chainAt h7 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore exit_s294 (hcode_of_env c (by env_simp; exact henv)) (B := 40)
        haw ?_ (by decide) (M := 126) (by decide) ?_ ?_) ?_
      · rw [h52]; omega
      · gas_omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h52]; omega) (by decide)
  clear h7
  -- 295..300: bump the counter, back to the head
  have h9 := chainAt h8 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_exit exit_b295 exit_b295_ok (n := 4) exit_b295_bound rfl
      (exit_b295_shape c _ _ aw g₁ e₁ iW [cnt, head, tail])
      (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h8
  obtain ⟨aw', g', e', haw', hg', hr⟩ := h9
  exact ⟨aw', g', e', haw', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩


/-! ### The loop -/

/-- The memory after the first `i` items of a drain from head `head` have been
staged: item `j` at offset `68 · j`. -/
def drainMem (st₀ : EvmYul.State .EVM) (head : UInt256) (mem₀ : ByteArray) : Nat → ByteArray
  | 0 => mem₀
  | i + 1 => writeItem st₀ (drainMem st₀ head mem₀ i) (UInt256.ofNat 68 * UInt256.ofNat i)
      (base (UInt256.ofNat i) head)

/-- **`accum_loop` terminates after exactly `count` iterations**, with every
item staged in memory, the counter equal to the count and the three slots of each
item touched. -/
theorem drain_loop (st₀ : EvmYul.State .EVM) (henv₀ : st₀.executionEnv = c.env)
    (head tail cnt : UInt256) (mem₀ : ByteArray) (hcnt : cnt.toNat ≤ 16) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e : Nat), i + m = cnt.toNat →
      Touched st₀ st → aw.toNat ≤ 40 → 7000 * m + 25 ≤ g.toNat →
      ∃ (st' : EvmYul.State .EVM) (aw' g' : UInt256) (e' : Nat), Touched st₀ st' ∧
        aw'.toNat ≤ 40 ∧ g.toNat - (7000 * m + 25) ≤ g'.toNat ∧
        ReachesLe exitJumpdests (42 * m + 6)
          (at_ c st (drainMem st₀ head mem₀ i) aw g 247
            (UInt256.ofNat i :: cnt :: head :: tail :: []) e)
          (at_ c st' (drainMem st₀ head mem₀ cnt.toNat) aw' g' 301
            (cnt :: cnt :: head :: tail :: []) e') := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e hi hst haw hg
    have hi' : i = cnt.toNat := by omega
    subst hi'
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hcode := hcode_of_env c henv
    have hcnt' : UInt256.ofNat cnt.toNat = cnt := ofNat_toNat' cnt
    have h1 := block_step hvj_exit exit_b247 exit_b247_ok (n := 5) exit_b247_bound rfl
      (exit_b247_shape c st (drainMem st₀ head mem₀ cnt.toNat) aw g e (UInt256.ofNat cnt.toNat)
        cnt [head, tail]) hcode rfl (by gas_omega) (by simp)
    have h2 := chain h1 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken exit_s254 hcode ((eq_ne_zero_iff _ _).mpr hcnt')
        (hvj_exit 301 (by decide)) (by gas_omega) (by simp)
    obtain ⟨g', e', hg', hr⟩ := h2
    rw [hcnt'] at hr ⊢
    exact ⟨st, aw, g', e', hst, haw, by gas_omega, Reaches.le hr (by gas_omega)⟩
  | succ m ih =>
    intro i st aw g e hi hst haw hg
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hi15 : (UInt256.ofNat i).toNat ≤ 15 := by
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]; omega
    have hne : UInt256.ofNat i ≠ cnt := by
      intro h
      have := congrArg UInt256.toNat h
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
      omega
    obtain ⟨aw₁, g₁, e₁, haw₁, hg₁, hr₁⟩ :=
      drain_body c (mem := drainMem st₀ head mem₀ i) (g := g) (e := e) (UInt256.ofNat i) cnt head
        tail henv hi15 hne haw (by gas_omega)
    rw [writeItem_of_touched hst, ofNat_add_ofNat, Nat.add_comm 1 i] at hr₁
    obtain ⟨st', aw', g', e', hst', haw', hg', hr'⟩ :=
      ih (i + 1) (touchItem st (base (UInt256.ofNat i) head)) aw₁ g₁ e₁ (by omega)
        (touched_touchItem hst _) haw₁ (by gas_omega)
    refine ⟨st', aw', g', e', hst', haw', by gas_omega, ?_⟩
    exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)

/-! ### `update_head` and `update_excess` -/

/-- The control words after `update_head`: a full drain resets both pointers,
otherwise the head advances by the drained count. -/
def headStore (cnt : UInt256) (st : EvmYul.State .EVM) : EvmYul.State .EVM :=
  if tailWord₀ c = headWord₀ c + cnt then
    (st.sstore (UInt256.ofNat 2) (UInt256.ofNat 0)).sstore (UInt256.ofNat 3) (UInt256.ofNat 0)
  else st.sstore (UInt256.ofNat 2) (headWord₀ c + cnt)

theorem update_head {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 44500 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 44500 ≤ g'.toNat ∧
      ReachesLe exitJumpdests 20
        (at_ c st mem aw g 301 (cnt :: cnt :: headWord₀ c :: tailWord₀ c :: []) e)
        (at_ c (headStore c cnt st) mem aw g' 330 (cnt :: []) e') := by
  have hcode := hcode_of_env c henv
  have h1 := le_of_exact <| block_step hvj_exit exit_b301 exit_b301_ok (n := 7)
    exit_b301_bound rfl (exit_b301_shape c st mem aw g e cnt cnt (headWord₀ c) (tailWord₀ c) [])
    hcode rfl (by gas_omega) (by simp)
  by_cases hfull : tailWord₀ c = headWord₀ c + cnt
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s310 hcode ((eq_ne_zero_iff _ _).mpr hfull)
        (hvj_exit 319 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b319 exit_b319_ok (n := 5) exit_b319_bound rfl
        (exit_b319_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega)
        (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s325 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b326 exit_b326_ok (n := 2) exit_b326_bound rfl
        (exit_b326_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s329 (hcode_of_env c (by env_simp; exact henv))
        (perm_of_env c (by env_simp; exact henv) hperm) (by gas_omega) (by simp)
    clear h5
    obtain ⟨g', e', hg', hr⟩ := h6
    simp only [headStore, if_pos hfull]
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s310 hcode ((eq_eq_zero_iff _ _).mpr hfull) (by gas_omega)
        (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b311 exit_b311_ok (n := 2) exit_b311_bound rfl
        (exit_b311_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega)
        (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore exit_s314 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b315 exit_b315_ok (n := 2) exit_b315_bound rfl
        (exit_b315_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    obtain ⟨g', e', hg', hr⟩ := h5
    simp only [headStore, if_neg hfull]
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩

/-- The excess word `update_excess` stores, read off the state `stX` it reads
from: `INHIBITOR` on nonempty calldata; zero when inhibited; otherwise the
folded excess above the target of `2`, or zero. -/
def newExcess (stX : EvmYul.State .EVM) : UInt256 :=
  if cdsizeWord c ≠ ⟨0⟩ then INH
  else if slotW stX (UInt256.ofNat 0) = INH then UInt256.ofNat 0
  else if UInt256.ofNat 2 < slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0) then
    (slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)) - UInt256.ofNat 2
  else UInt256.ofNat 0

theorem update_excess {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 50000 ≤ g.toNat) :
    ∃ (stX : EvmYul.State .EVM) (g' : UInt256) (e' : Nat), Touched st stX ∧
      g.toNat - 50000 ≤ g'.toNat ∧
      ReachesLe exitJumpdests 36 (at_ c st mem aw g 330 (cnt :: []) e)
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
          (UInt256.ofNat 0)) mem aw g' 453 (UInt256.ofNat 0 :: (UInt256.ofNat 68 * cnt) :: []) e') := by
  have hcode := hcode_of_env c henv
  have hcds : cdsizeW st = cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  have h1 := le_of_exact <| block_step hvj_exit exit_b330 exit_b330_ok (n := 3)
    exit_b330_bound rfl (exit_b330_shape c st mem aw g e [cnt]) hcode rfl (by gas_omega) (by simp)
  simp only [hcds] at h1
  -- the tail from `store_excess` (442), shared by every branch
  have tail : ∀ (stX : EvmYul.State .EVM) (v g₁ : UInt256) (e₁ : Nat), Touched st stX →
      g₁.toNat ≥ g.toNat - 5000 →
      ∃ (g' : UInt256) (e' : Nat), g₁.toNat - 44300 ≤ g'.toNat ∧
        ReachesLe exitJumpdests 9 (at_ c stX mem aw g₁ 442 (v :: cnt :: []) e₁)
          (at_ c ((stX.sstore (UInt256.ofNat 0) v).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)) mem aw
            g' 453 (UInt256.ofNat 0 :: (UInt256.ofNat 68 * cnt) :: []) e') := by
    intro stX v g₁ e₁ hstX hg₁
    have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henv
    have hcodeX := hcode_of_env c henvX
    have t1 := le_of_exact <| block_step hvj_exit exit_b442 exit_b442_ok (n := 2)
      exit_b442_bound rfl (exit_b442_shape c stX mem aw g₁ e₁ [v, cnt]) hcodeX rfl (by gas_omega)
      (by simp)
    have t2 := chainLe t1 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore exit_s444 hcodeX (perm_of_env c henvX hperm) (by gas_omega) (by simp)
    clear t1
    have t3 := chainLe t2 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_exit exit_b445 exit_b445_ok (n := 2) exit_b445_bound rfl
        (exit_b445_shape c _ mem aw g₂ e₂ [cnt]) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t2
    have t4 := chainLe t3 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore exit_s448 (hcode_of_env c (by env_simp; exact henvX))
        (perm_of_env c (by env_simp; exact henvX) hperm) (by gas_omega) (by simp)
    clear t3
    have t5 := chainLe t4 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_exit exit_b449 exit_b449_ok (n := 3) exit_b449_bound rfl
        (exit_b449_shape c _ mem aw g₂ e₂ cnt []) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t4
    obtain ⟨g', e', hg', hr⟩ := t5
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  by_cases hcd : cdsizeWord c ≠ ⟨0⟩
  · -- nonempty calldata: latch the inhibitor
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken exit_s335 hcode hcd (hvj_exit 408 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b408 exit_b408_ok (n := 2) exit_b408_bound rfl
        (exit_b408_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h3
    obtain ⟨g', e', hg', hr'⟩ := tail st INH g₁ e₁ (Touched.refl st) (by gas_omega)
    refine ⟨st, g', e', Touched.refl st, by gas_omega, ?_⟩
    simp only [newExcess, if_pos hcd]
    exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
  · have hcd' : cdsizeWord c = ⟨0⟩ := by
      by_contra h; exact hcd h
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough exit_s335 hcode hcd' (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_exit exit_b336 exit_b336_ok (n := 8) exit_b336_bound rfl
        (exit_b336_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    simp only [slotW_touch] at h3
    have hstX : Touched st (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) :=
      ((Touched.refl st).touch _).touch _
    have hcodeX : (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)).executionEnv.code
        = exitRuntime := hcode
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_taken exit_s379 hcodeX ((eq_ne_zero_iff _ _).mpr hinh.symm)
          (hvj_exit 390 (by decide)) (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_exit exit_b390 exit_b390_ok (n := 6) exit_b390_bound rfl
          (exit_b390_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h5
      obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
      refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
      simp only [newExcess, if_neg hcd, slotW_touch, if_pos hinh]
      exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_fallthrough exit_s379 hcodeX ((eq_eq_zero_iff _ _).mpr (fun h => hinh h.symm))
          (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_exit exit_b380 exit_b380_ok (n := 6) exit_b380_bound rfl
          (exit_b380_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      by_cases hgt : UInt256.ofNat 2 < slotW st (UInt256.ofNat 1) + slotW st (UInt256.ofNat 0)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_taken exit_s389 hcodeX ((gt_ne_zero_iff _ _).mpr hgt)
            (hvj_exit 398 (by decide)) (by gas_omega) (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_exit exit_b398 exit_b398_ok (n := 7) exit_b398_bound rfl
            (exit_b398_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ _ g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_pos hgt]
        exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_fallthrough exit_s389 hcodeX ((gt_eq_zero_iff _ _).mpr hgt) (by gas_omega)
            (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_exit exit_b390 exit_b390_ok (n := 6) exit_b390_bound rfl
            (exit_b390_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_neg hgt]
        exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)

/-! ### The system endpoint -/

theorem drainWord_le : (drainWord c).toNat ≤ 16 := by
  unfold drainWord
  split
  · rename_i h
    have := (toNat_lt_iff _ _).mp h
    rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
    omega
  · rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]

theorem touched_stP : Touched (entrySt c) (stP c) := ((Touched.refl _).touch _).touch _

/-- **The system call returns.** For `SYSTEM_ADDR` with write permission, the
run drains `min(tail − head, 16)` items into memory, rewrites the four control
words, and halts on `RETURN` publishing the staged records. -/
theorem system_returns (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 250000 ≤ c.gas.toNat) :
    ∃ (st' stX : EvmYul.State .EVM) (aw g : UInt256) (e : Nat),
      Touched (entrySt c) st' ∧ Touched (headStore c (drainWord c) st') stX ∧
      Ends c 800
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 453
          (UInt256.ofNat 0 :: (UInt256.ofNat 68 * drainWord c) :: []) e) .RETURN
        ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 68 * drainWord c).toNat) := by
  obtain ⟨g₀, e₀, hg₀, hpre⟩ := system_prefix c hsys (by gas_omega)
  have hcnt := drainWord_le c
  obtain ⟨st', aw', g₁, e₁, hst', haw', hg₁, hloop⟩ := drain_loop c (entrySt c) rfl (headWord₀ c)
    (tailWord₀ c) (drainWord c) (mem₀ c) hcnt (drainWord c).toNat 0 (stP c) (aw₀ c) g₀ e₀
    (by omega) (touched_stP c) (by rw [activeWords_entry]; omega) (by gas_omega)
  have h1 : ∃ (g : UInt256) (e : Nat), c.gas.toNat - 116400 ≤ g.toNat ∧
      ReachesLe exitJumpdests 703 c.entry
        (at_ c st' (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 301
          (drainWord c :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) :=
    ⟨g₁, e₁, by gas_omega, ReachesLe.mono (hpre.trans hloop) (by gas_omega)⟩
  have henv' : st'.executionEnv = c.env := hst'.executionEnv
  have h2 := chainLe h1 fun g e hg => update_head c henv' hperm (drainWord c) (by gas_omega)
  clear h1
  have henvH : (headStore c (drainWord c) st').executionEnv = c.env := by
    unfold headStore; split <;> (env_simp; exact henv')
  have h3 : ∃ (stX : EvmYul.State .EVM) (g : UInt256) (e : Nat),
      Touched (headStore c (drainWord c) st') stX ∧ c.gas.toNat - 210900 ≤ g.toNat ∧
      ReachesLe exitJumpdests (703 + 20 + 36) c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 453
          (UInt256.ofNat 0 :: (UInt256.ofNat 68 * drainWord c) :: []) e) := by
    obtain ⟨g₂, e₂, hg₂, hr₂⟩ := h2
    obtain ⟨stX, g₃, e₃, hstX, hg₃, hr₃⟩ := update_excess c
      (mem := drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) (aw := aw')
      (g := g₂) (e := e₂) henvH hperm (drainWord c) (by gas_omega)
    exact ⟨stX, g₃, e₃, hstX, by gas_omega, hr₂.trans hr₃⟩
  clear h2
  obtain ⟨stX, g, e, hstX, hgX, hr⟩ := h3
  have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henvH
  refine ⟨st', stX, aw', g, e, hst', hstX, ReachesLe.mono hr (by gas_omega), ?_⟩
  have hlen : (UInt256.ofNat 68 * drainWord c).toNat = 68 * (drainWord c).toNat :=
    toNat_ofNat_mul_of_lt 68 _ (by rw [size_eq]; omega)
  refine halt_RETURN exit_s453 (hcode_of_env c (by env_simp; exact henvX)) (B := 40) (M := 123)
    (g := g) haw' ?_ (by decide) (by decide) ?_ (by simp)
  · rw [hlen]; show (0 + 68 * (drainWord c).toNat + 31) / 32 ≤ 40; omega
  · gas_omega

end Eip8282.Audit.EntryReach.Exit
