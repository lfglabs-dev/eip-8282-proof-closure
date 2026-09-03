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
    st.executionEnv.code = depositRuntime := by
  rw [h]; exact c.code_pinned

/-! ## The opening gate -/

/-- `CALLER; PUSH20 SYSTEM_ADDR; EQ; PUSH2 @read_requests` from the entry machine. -/
theorem gate (hg : 11 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
      Reaches depositJumpdests 4 c.entry
        (at_ c (entrySt c) c.entry.memory c.entry.activeWords g 26
          (UInt256.ofNat 284 :: UInt256.eq sysW (callerWord c) :: []) e) := by
  change ∃ (g : UInt256) (e : Nat), c.gas.toNat - 11 ≤ g.toNat ∧
    Reaches depositJumpdests 4 (at_ c (entrySt c) c.entry.memory c.entry.activeWords c.gas 0 [] 0) _
  exact block_step hvj_deposit deposit_b0 deposit_b0_ok (n := 4) deposit_b0_bound rfl
    (deposit_b0_shape c (entrySt c) _ _ c.gas 0 []) (hcode_of_env c rfl) rfl hg (by simp)

/-! ## The user path up to the fee loop -/

/-- `bump_excess`: the excess the fee loop is quoted at. -/
def effExcess : UInt256 :=
  if 8 < (countWord c).toNat then (countWord c - UInt256.ofNat 8) + excessWord c
  else excessWord c

/-- From the fall-through of the gate (`pc = 27`) to the fee loop head, on an
uninhibited image: the excess and count are read, `bump_excess` is resolved, and
the loop is entered with output `0`, accumulator `17 · 1` and counter `1`. -/
theorem to_fee_loop {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (hen : excessWord c ≠ INH) (hg : 4300 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 4300 ≤ g'.toNat ∧
      ReachesLe depositJumpdests 29 (at_ c (entrySt c) mem aw g 27 [] e)
        (at_ c (st₂ c) mem aw g' 100
          (UInt256.ofNat 0 :: (UInt256.ofNat 17 * UInt256.ofNat 1) :: UInt256.ofNat 1 ::
            effExcess c :: UInt256.ofNat 17 :: []) e') := by
  -- 27..64: the inhibitor test
  have h1 := block_step hvj_deposit deposit_b27 deposit_b27_ok (n := 6) deposit_b27_bound rfl
    (deposit_b27_shape c (entrySt c) mem aw g e []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  -- 67: not taken
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough deposit_s67 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => hen h.symm)) (by gas_omega)
      (by simp)
  clear h1
  -- 68..75: the count test
  have h3 := chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_deposit deposit_b68 deposit_b68_ok (n := 6) deposit_b68_bound rfl
      (deposit_b68_shape c _ mem aw g₁ e₁ [excessWord c]) (hcode_of_env c rfl) rfl
      (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hcnt : 8 < (countWord c).toNat
  · -- bump_excess taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken deposit_s77 (hcode_of_env c rfl)
        ((gt_ne_zero_iff _ _).mpr ((ofNat_lt_iff (by decide) _).mpr hcnt))
        (hvj_deposit 82 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b82 deposit_b82_ok (n := 5) deposit_b82_bound rfl
        (deposit_b82_shape c _ mem aw g₁ e₁ (countWord c) (excessWord c) [])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b88 deposit_b88_ok (n := 9) deposit_b88_bound rfl
        (deposit_b88_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by gas_omega)
        (by simp)
    clear h5
    simp only [effExcess, if_pos hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by gas_omega, Reaches.le hr (by decide)⟩
  · -- bump_excess not taken
    have h4 := chain h3 fun g₁ e₁ hg₁ =>
      reach_jumpi_fallthrough deposit_s77 (hcode_of_env c rfl)
        ((gt_eq_zero_iff _ _).mpr (fun h => hcnt ((ofNat_lt_iff (by decide) _).mp h)))
        (by gas_omega) (by simp)
    clear h3
    have h5 := chain h4 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b78 deposit_b78_ok (n := 3) deposit_b78_bound rfl
        (deposit_b78_shape c _ mem aw g₁ e₁ (countWord c) [excessWord c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chain h5 fun g₁ e₁ hg₁ =>
      block_step hvj_deposit deposit_b88 deposit_b88_ok (n := 9) deposit_b88_bound rfl
        (deposit_b88_shape c _ mem aw g₁ e₁ _ []) (hcode_of_env c rfl) rfl (by gas_omega)
        (by simp)
    clear h5
    simp only [effExcess, if_neg hcnt]
    obtain ⟨g', e', hg', hr⟩ := h6
    exact ⟨g', e', by gas_omega, Reaches.le hr (by decide)⟩


/-! ## The fee loop

`fake_expo` runs `[out, acc, i, X, 17] ↦ [acc + out, X·acc / (i·17), 1 + i, X, 17]`
until `acc = 0`; `feeExit` (in `Path`) is that recurrence on words. -/

/-- One pass of the loop head onto the taken exit branch, at `acc = 0`. -/
theorem fee_head_exit {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o i X : UInt256) (hg : 25 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 25 ≤ g'.toNat ∧
      Reaches depositJumpdests 7
        (at_ c st mem aw g 100 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 127 (o :: ⟨0⟩ :: i :: X :: UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_deposit deposit_b100 deposit_b100_ok (n := 6) deposit_b100_bound rfl
    (deposit_b100_shape c st mem aw g e o ⟨0⟩ [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by gas_omega) (by simp)
  exact chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_taken deposit_s107 (hcode_of_env c henv) ((feeLoop_exit_iff _).mpr rfl)
      (hvj_deposit 127 (by decide)) (by gas_omega) (by simp)

/-- One full iteration of the loop, at `acc ≠ 0`. -/
theorem fee_iteration {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (o a i X : UInt256) (ha : a ≠ ⟨0⟩) (hg : 87 ≤ g.toNat) :
    ∃ (g' : UInt256) (e' : Nat), g.toNat - 87 ≤ g'.toNat ∧
      Reaches depositJumpdests 24
        (at_ c st mem aw g 100 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
        (at_ c st mem aw g' 100
          ((a + o) :: ((X * a) / (i * UInt256.ofNat 17)) :: (UInt256.ofNat 1 + i) :: X ::
            UInt256.ofNat 17 :: []) e') := by
  have h1 := block_step hvj_deposit deposit_b100 deposit_b100_ok (n := 6) deposit_b100_bound rfl
    (deposit_b100_shape c st mem aw g e o a [i, X, UInt256.ofNat 17]) (hcode_of_env c henv) rfl
    (by gas_omega) (by simp)
  have h2 := chain h1 fun g₁ e₁ hg₁ =>
    reach_jumpi_fallthrough deposit_s107 (hcode_of_env c henv) ((feeLoop_continue_iff _).mpr ha)
      (by gas_omega) (by simp)
  clear h1
  exact chain h2 fun g₁ e₁ hg₁ =>
    block_step hvj_deposit deposit_b108 deposit_b108_ok (n := 17) deposit_b108_bound rfl
      (deposit_b108_shape c st mem aw g₁ e₁ o a i X (UInt256.ofNat 17) []) (hcode_of_env c henv) rfl
      (by gas_omega) (by simp)

/-- **The fee loop terminates where `feeExit` says it does.** From the loop head
with `n` iterations of budget left, the run lands on the exit block with the
output and counter `feeExit` computes, in at most `24 · n + 7` iterations of `X`. -/
theorem fee_loop {st : EvmYul.State .EVM} {mem : ByteArray} {aw : UInt256} (X : UInt256)
    (henv : st.executionEnv = c.env) :
    ∀ (n : Nat) (o a i g : UInt256) (e : Nat) (o' i' : UInt256),
      feeExit X n o a i = some (o', i') → 87 * n + 25 ≤ g.toNat →
      ∃ (g' : UInt256) (e' : Nat), g.toNat - (87 * n + 25) ≤ g'.toNat ∧
        ReachesLe depositJumpdests (24 * n + 7)
          (at_ c st mem aw g 100 (o :: a :: i :: X :: UInt256.ofNat 17 :: []) e)
          (at_ c st mem aw g' 127 (o' :: ⟨0⟩ :: i' :: X :: UInt256.ofNat 17 :: []) e') := by
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
on an uninhibited image whose fee loop terminates within `n` iterations. The
machine stands on the `JUMPI @handle_input` with the fee quoted. -/
theorem user_prefix (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256}
    (hfee : feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
      (UInt256.ofNat 1) = some (o', i'))
    (hg : 87 * n + 4400 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - (87 * n + 4400) ≤ g.toNat ∧
      ReachesLe depositJumpdests (24 * n + 60) c.entry
        (at_ c (st₂ c) c.entry.memory c.entry.activeWords g 142
          (UInt256.ofNat 159 :: UInt256.eq (UInt256.ofNat 184) (cdsizeWord c) ::
            feeWord o' :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_fallthrough deposit_s26 (hcode_of_env c rfl)
      ((eq_eq_zero_iff _ _).mpr (fun h => huser h.symm)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => to_fee_loop c hen (by gas_omega)
  clear h2
  have h4 := chainLe h3 fun g₁ e₁ hg₁ =>
    fee_loop c (effExcess c) rfl n _ _ _ g₁ e₁ o' i' hfee (by gas_omega)
  clear h3
  have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b127 deposit_b127_ok (n := 13) deposit_b127_bound rfl
      (deposit_b127_shape c (st₂ c) _ _ g₁ e₁ o' ⟨0⟩ i' (effExcess c) (UInt256.ofNat 17) [])
      (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h4
  simp only [cdsizeW_touch] at h5
  obtain ⟨g, e, hg', hr⟩ := h5
  exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩


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

abbrev mem₀ : ByteArray := c.entry.memory
abbrev aw₀ : UInt256 := c.entry.activeWords

/-- The fee-loop hypothesis every uninhibited user endpoint carries. -/
abbrev FeeLoopEnds (n : Nat) (o' i' : UInt256) : Prop :=
  feeExit (effExcess c) n (UInt256.ofNat 0) (UInt256.ofNat 17 * UInt256.ofNat 1)
    (UInt256.ofNat 1) = some (o', i')

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

/-- **Fee getter.** Empty calldata, zero value: the fee word is stored at memory
`0` and the 32-byte slice is returned. -/
theorem user_getter_returns (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = ⟨0⟩) (hval : valueWord c = ⟨0⟩)
    (hg : 87 * n + 4500 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 80)
        (at_ c (st₂ c) (mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o'))
          (mAfter (aw₀ c) 0 32) g 158 (UInt256.ofNat 0 :: UInt256.ofNat 32 :: []) e) .RETURN
        ((mstoreMem (mem₀ c) (UInt256.ofNat 0) (feeWord o')).readWithPadding 0 32) := by
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
    reach_jumpi_fallthrough deposit_s152 (hcode_of_env c rfl) hval (by gas_omega) (by simp)
  clear h5
  have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b153 deposit_b153_ok (n := 1) deposit_b153_bound rfl
      (deposit_b153_shape c (st₂ c) _ _ g₁ e₁ [feeWord o']) (hcode_of_env c rfl) rfl (by gas_omega)
      (by simp)
  clear h6
  have h8 := chainLe h7 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_mstore deposit_s154 (hcode_of_env c rfl) (B := 1) (by rw [activeWords_entry]; omega)
      (by decide) (by decide) (M := 6) (by decide) (by gas_omega) (by simp)
  clear h7
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b155 deposit_b155_ok (n := 2) deposit_b155_bound rfl
      (deposit_b155_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h8
  obtain ⟨g', e', hg', hr'⟩ := h9
  refine ⟨g', e', ReachesLe.mono hr' (by gas_omega), ?_⟩
  refine halt_RETURN deposit_s158 (hcode_of_env c rfl) (B := 1) (M := 3) (g := g') ?_ ?_ ?_ ?_ ?_ ?_
  · exact toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide)
  · decide
  · decide
  · decide
  · omega
  · simp

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

/-- The masked `uint64` amount word `handle_input` extracts from calldata bytes
`80..88`. -/
abbrev amountWord : UInt256 :=
  UInt256.land (UInt256.ofNat 18446744073709551615) (cdW (entrySt c) (UInt256.ofNat 56))

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

abbrev countStore : EvmYul.State .EVM :=
  (touch (st₂ c) (UInt256.ofNat 1)).sstore (UInt256.ofNat 1) (UInt256.ofNat 1 + countWord c)
abbrev tailWord : UInt256 := slotW (countStore c) (UInt256.ofNat 3)
abbrev slotBase : UInt256 := UInt256.ofNat 4 + (UInt256.ofNat 6 * tailWord c)
abbrev dw (off : Nat) : UInt256 := cdW (entrySt c) (UInt256.ofNat off)

/-- The six item words stored, slot by slot. -/
abbrev itemStored : EvmYul.State .EVM :=
  (((((((touch (countStore c) (UInt256.ofNat 3)).sstore (slotBase c) (dw c 0)).sstore
    (UInt256.ofNat 1 + slotBase c) (dw c 32)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c)) (dw c 64)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c))) (dw c 96)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + slotBase c))))
    (dw c 128)).sstore
    (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 + (UInt256.ofNat 1 +
      (UInt256.ofNat 1 + slotBase c))))) (dw c 160))

/-- Memory after the record is staged: the 184 calldata bytes at offset `0`. -/
abbrev stagedMem : ByteArray :=
  cdcopyMem (itemStored c) (mem₀ c) (UInt256.ofNat 0) (UInt256.ofNat 0) (UInt256.ofNat 184)

/-- The final state: item stored, receipt logged, `QUEUE_TAIL` advanced. -/
abbrev appendedSt : EvmYul.State .EVM :=
  (logged (itemStored c) ((stagedMem c).readWithPadding 0 184)).sstore (UInt256.ofNat 3)
    (UInt256.ofNat 1 + tailWord c)

/-- **Accepted submission.** 184-byte calldata, the fee paid, the amount at or
above the floor and the stake covered: the record is stored and logged and the
run halts on `STOP`. Write permission is required, exactly as `Z` demands at the
first `SSTORE`. -/
theorem user_append_stops (huser : callerWord c ≠ sysW) (hen : excessWord c ≠ INH)
    (hperm : c.env.perm = true)
    {n : Nat} {o' i' : UInt256} (hfee : FeeLoopEnds c n o' i')
    (hsize : cdsizeWord c = UInt256.ofNat 184) (hpaid : ¬ valueWord c < feeWord o')
    (hfloor : ¬ amountWord c < UInt256.ofNat 1000000000)
    (hstake : ¬ (valueWord c - feeWord o') < UInt256.ofNat 1000000000 * amountWord c)
    (hg : 87 * n + 190000 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat),
      Ends c (24 * n + 150)
        (at_ c (appendedSt c) (stagedMem c) (mAfter (mAfter (aw₀ c) 0 184) 0 184) g 283 [] e)
        .STOP .empty := by
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
    reach_jumpi_fallthrough deposit_s204 (hcode_of_env c rfl) ((lt_eq_zero_iff _ _).mpr hstake)
      (by gas_omega) (by simp)
  clear h7
  -- 205..212: bump the count
  have h9 := chainLe h8 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b205 deposit_b205_ok (n := 5) deposit_b205_bound rfl
      (deposit_b205_shape c (st₂ c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h8
  simp only [slotW_touch] at h9
  have h10 := chainLe h9 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s213 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h9
  -- 214..226: base slot and the first item word
  have h11 := chainLe h10 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b214 deposit_b214_ok (n := 10) deposit_b214_bound rfl
      (deposit_b214_shape c (countStore c) _ _ g₁ e₁ []) (hcode_of_env c (by env_simp)) rfl
      (by gas_omega) (by simp)
  clear h10
  simp only [cdW_touch, cdW_sstore] at h11
  have h12 := chainLe h11 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s227 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h11
  have h13 := chainLe h12 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b228 deposit_b228_ok (n := 5) deposit_b228_bound rfl
      (deposit_b228_shape c _ _ _ g₁ e₁ (slotBase c) [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h12
  simp only [cdW_touch, cdW_sstore] at h13
  have h14 := chainLe h13 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s235 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h13
  have h15 := chainLe h14 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b236 deposit_b236_ok (n := 5) deposit_b236_bound rfl
      (deposit_b236_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h14
  simp only [cdW_touch, cdW_sstore] at h15
  have h16 := chainLe h15 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s243 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h15
  have h17 := chainLe h16 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b244 deposit_b244_ok (n := 5) deposit_b244_bound rfl
      (deposit_b244_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h16
  simp only [cdW_touch, cdW_sstore] at h17
  have h18 := chainLe h17 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s251 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h17
  have h19 := chainLe h18 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b252 deposit_b252_ok (n := 5) deposit_b252_bound rfl
      (deposit_b252_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h18
  simp only [cdW_touch, cdW_sstore] at h19
  have h20 := chainLe h19 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s259 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h19
  have h21 := chainLe h20 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b260 deposit_b260_ok (n := 5) deposit_b260_bound rfl
      (deposit_b260_shape c _ _ _ g₁ e₁ _ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h20
  simp only [cdW_touch, cdW_sstore] at h21
  have h22 := chainLe h21 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s267 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h21
  -- 268..276: stage and log the record
  have h23 := chainLe h22 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b268 deposit_b268_ok (n := 3) deposit_b268_bound rfl
      (deposit_b268_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h22
  have h24 := chainLe h23 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_calldatacopy deposit_s272 (hcode_of_env c (by env_simp)) (B := 6)
      (by rw [activeWords_entry]; omega) (by decide) (by decide) (M := 39) (by decide) (by gas_omega)
      (by simp)
  clear h23
  have h25 := chainLe h24 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b273 deposit_b273_ok (n := 2) deposit_b273_bound rfl
      (deposit_b273_shape c (itemStored c) _ _ g₁ e₁ [tailWord c]) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h24
  have h26 := chainLe h25 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_log0 deposit_s276 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (B := 6) (toNat_mAfter_le (by rw [activeWords_entry]; omega) (by decide) (by decide))
      (by decide) (by decide) (M := 1865) (by decide) (by gas_omega) (by simp)
  clear h25
  -- 277..282: advance the tail
  have h27 := chainLe h26 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b277 deposit_b277_ok (n := 3) deposit_b277_bound rfl
      (deposit_b277_shape c _ _ _ g₁ e₁ (tailWord c) []) (hcode_of_env c (by env_simp))
      rfl (by gas_omega) (by simp)
  clear h26
  have h28 := chainLe h27 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_sstore deposit_s282 (hcode_of_env c (by env_simp)) (perm_of_env c (by env_simp) hperm)
      (by gas_omega) (by simp)
  clear h27
  obtain ⟨g', e', _, hr'⟩ := h28
  refine ⟨g', e', ReachesLe.mono hr' (by gas_omega), ?_⟩
  exact halt_STOP deposit_s283 (hcode_of_env c (by env_simp)) (by simp)


/-! ## The system path

`read_requests` reads the queue pointers, clamps the count at `MAX_PER_BLOCK`,
runs `accum_loop` once per drained item, updates the pointers, folds the excess
and returns the staged records. -/

abbrev tailWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 3)
abbrev headWord₀ : UInt256 := slotW (entrySt c) (UInt256.ofNat 2)
/-- `tail - head`, as the `SUB` computes it. -/
abbrev queueLen : UInt256 := tailWord₀ c - headWord₀ c
/-- `min(tail - head, 64)`: the number of items drained. -/
def drainWord : UInt256 :=
  if queueLen c < UInt256.ofNat 64 then queueLen c else UInt256.ofNat 64

/-- The state after the two pointer reads. -/
abbrev stP : EvmYul.State .EVM := touch (touch (entrySt c) (UInt256.ofNat 3)) (UInt256.ofNat 2)

/-- **From the entry machine to the loop head**, for the system caller. -/
theorem system_prefix (hsys : callerWord c = sysW) (hg : 4300 ≤ c.gas.toNat) :
    ∃ (g : UInt256) (e : Nat), c.gas.toNat - 4300 ≤ g.toNat ∧
      ReachesLe depositJumpdests 25 c.entry
        (at_ c (stP c) (mem₀ c) (aw₀ c) g 307
          (UInt256.ofNat 0 :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) := by
  have h1 := le_of_exact (gate c (by gas_omega))
  have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
    reach_jumpi_taken deposit_s26 (hcode_of_env c rfl) ((eq_ne_zero_iff _ _).mpr hsys.symm)
      (hvj_deposit 284 (by decide)) (by gas_omega) (by simp)
  clear h1
  have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
    block_step hvj_deposit deposit_b284 deposit_b284_ok (n := 12) deposit_b284_bound rfl
      (deposit_b284_shape c (entrySt c) _ _ g₁ e₁ []) (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
  clear h2
  simp only [slotW_touch] at h3
  by_cases hlt : queueLen c < UInt256.ofNat 64
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s301 (hcode_of_env c rfl) ((gt_ne_zero_iff _ _).mpr hlt)
        (hvj_deposit 305 (by decide)) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [queueLen c, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    simp only [drainWord, if_pos hlt]
    obtain ⟨g, e, hg', hr⟩ := h5
    exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s301 (hcode_of_env c rfl) ((gt_eq_zero_iff _ _).mpr hlt)
        (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b302 deposit_b302_ok (n := 2) deposit_b302_bound rfl
        (deposit_b302_shape c (stP c) _ _ g₁ e₁ (queueLen c) [headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b305 deposit_b305_ok (n := 2) deposit_b305_bound rfl
        (deposit_b305_shape c (stP c) _ _ g₁ e₁ [UInt256.ofNat 64, headWord₀ c, tailWord₀ c])
        (hcode_of_env c rfl) rfl (by gas_omega) (by simp)
    clear h5
    simp only [drainWord, if_neg hlt]
    obtain ⟨g, e, hg', hr⟩ := h6
    exact ⟨g, e, by gas_omega, ReachesLe.mono hr (by gas_omega)⟩

/-! ### One iteration of `accum_loop` -/

/-- **What one `accum_loop` iteration writes.** The six words of the packed
item at `base` go to `off, off+32, …, off+160`; the amount field is re-written
byte by byte, little-endian, at `off+80`. Stated exactly as the pinned code
computes each operand, so that the body lemma is a unification. -/
def writeItem (st : EvmYul.State .EVM) (mem : ByteArray) (off base : UInt256) : ByteArray :=
  let w2 := slotW st (UInt256.ofNat 2 + base)
  let off32 := UInt256.ofNat 32 + off
  let off64 := UInt256.ofNat 32 + off32
  let am := UInt256.land mask (UInt256.shiftRight w2 (UInt256.ofNat 64))
  let off80 := UInt256.ofNat 16 + off64
  let off96 := UInt256.ofNat 32 + off64
  let off128 := UInt256.ofNat 32 + off96
  let off160 := UInt256.ofNat 32 + off128
  let m := mstoreMem mem off (slotW st base)
  let m := mstoreMem m off32 (slotW st (UInt256.ofNat 1 + base))
  let m := mstoreMem m off64 w2
  let m := mstore8Mem m (UInt256.ofNat 7 + off80) (UInt256.shiftRight am (UInt256.ofNat 56))
  let m := mstore8Mem m (UInt256.ofNat 6 + off80) (UInt256.shiftRight am (UInt256.ofNat 48))
  let m := mstore8Mem m (UInt256.ofNat 5 + off80) (UInt256.shiftRight am (UInt256.ofNat 40))
  let m := mstore8Mem m (UInt256.ofNat 4 + off80) (UInt256.shiftRight am (UInt256.ofNat 32))
  let m := mstore8Mem m (UInt256.ofNat 3 + off80) (UInt256.shiftRight am (UInt256.ofNat 24))
  let m := mstore8Mem m (UInt256.ofNat 2 + off80) (UInt256.shiftRight am (UInt256.ofNat 16))
  let m := mstore8Mem m (UInt256.ofNat 1 + off80) (UInt256.shiftRight am (UInt256.ofNat 8))
  let m := mstore8Mem m off80 am
  let m := mstoreMem m off96 (slotW st (UInt256.ofNat 3 + base))
  let m := mstoreMem m off128 (slotW st (UInt256.ofNat 4 + base))
  mstoreMem m off160 (slotW st (UInt256.ofNat 5 + base))

/-- The offsets of one item, as naturals: with `i ≤ 63` nothing wraps. -/
theorem off_toNat {iW : UInt256} (hi : iW.toNat ≤ 63) :
    (UInt256.ofNat 184 * iW).toNat = 184 * iW.toNat :=
  toNat_ofNat_mul_of_lt 184 iW (by rw [size_eq]; omega)

theorem offk_toNat {iW : UInt256} (hi : iW.toNat ≤ 63) (k : Nat) (a : UInt256)
    (ha : a.toNat ≤ 184 * iW.toNat + 200) (hk : k ≤ 200) :
    (UInt256.ofNat k + a).toNat = k + a.toNat :=
  toNat_ofNat_add_of_lt k a (by rw [size_eq]; omega)

/-- The same bound holds for every offset the iteration touches: all are
`184 · i + t` with `t ≤ 192`, so the last byte written is below `12 000` and the
word count stays under `400`. -/
theorem item_offsets {iW : UInt256} (hi : iW.toNat ≤ 63) :
    let off := UInt256.ofNat 184 * iW
    let off32 := UInt256.ofNat 32 + off
    let off64 := UInt256.ofNat 32 + off32
    let off80 := UInt256.ofNat 16 + off64
    let off96 := UInt256.ofNat 32 + off64
    let off128 := UInt256.ofNat 32 + off96
    let off160 := UInt256.ofNat 32 + off128
    off.toNat = 184 * iW.toNat ∧ off32.toNat = 184 * iW.toNat + 32 ∧
      off64.toNat = 184 * iW.toNat + 64 ∧ off80.toNat = 184 * iW.toNat + 80 ∧
      off96.toNat = 184 * iW.toNat + 96 ∧ off128.toNat = 184 * iW.toNat + 128 ∧
      off160.toNat = 184 * iW.toNat + 160 ∧
      (UInt256.ofNat 7 + off80).toNat = 184 * iW.toNat + 87 ∧
      (UInt256.ofNat 6 + off80).toNat = 184 * iW.toNat + 86 ∧
      (UInt256.ofNat 5 + off80).toNat = 184 * iW.toNat + 85 ∧
      (UInt256.ofNat 4 + off80).toNat = 184 * iW.toNat + 84 ∧
      (UInt256.ofNat 3 + off80).toNat = 184 * iW.toNat + 83 ∧
      (UInt256.ofNat 2 + off80).toNat = 184 * iW.toNat + 82 ∧
      (UInt256.ofNat 1 + off80).toNat = 184 * iW.toNat + 81 := by
  intro off off32 off64 off80 off96 off128 off160
  have h0 : off.toNat = 184 * iW.toNat := off_toNat hi
  have h32 : off32.toNat = 184 * iW.toNat + 32 := by
    show (UInt256.ofNat 32 + off).toNat = _
    rw [offk_toNat hi 32 off (by gas_omega) (by gas_omega), h0]; omega
  have h64 : off64.toNat = 184 * iW.toNat + 64 := by
    show (UInt256.ofNat 32 + off32).toNat = _
    rw [offk_toNat hi 32 off32 (by gas_omega) (by gas_omega), h32]; omega
  have h80 : off80.toNat = 184 * iW.toNat + 80 := by
    show (UInt256.ofNat 16 + off64).toNat = _
    rw [offk_toNat hi 16 off64 (by gas_omega) (by gas_omega), h64]; omega
  have h96 : off96.toNat = 184 * iW.toNat + 96 := by
    show (UInt256.ofNat 32 + off64).toNat = _
    rw [offk_toNat hi 32 off64 (by gas_omega) (by gas_omega), h64]; omega
  have h128 : off128.toNat = 184 * iW.toNat + 128 := by
    show (UInt256.ofNat 32 + off96).toNat = _
    rw [offk_toNat hi 32 off96 (by gas_omega) (by gas_omega), h96]; omega
  have h160 : off160.toNat = 184 * iW.toNat + 160 := by
    show (UInt256.ofNat 32 + off128).toNat = _
    rw [offk_toNat hi 32 off128 (by gas_omega) (by gas_omega), h128]; omega
  refine ⟨h0, h32, h64, h80, h96, h128, h160, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [offk_toNat hi _ off80 (by gas_omega) (by gas_omega), h80]; omega)


/-- The base slot of item `i` of a queue whose head is `head`, as the code forms it. -/
abbrev base (iW head : UInt256) : UInt256 := UInt256.ofNat 4 + (UInt256.ofNat 6 * (iW + head))

/-- The six storage reads of one iteration, as touches. -/
abbrev touchItem (st : EvmYul.State .EVM) (b : UInt256) : EvmYul.State .EVM :=
  touch (touch (touch (touch (touch (touch st b) (UInt256.ofNat 1 + b)) (UInt256.ofNat 2 + b))
    (UInt256.ofNat 3 + b)) (UInt256.ofNat 4 + b)) (UInt256.ofNat 5 + b)

theorem touched_touchItem {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (b : UInt256) :
    Touched st₀ (touchItem st b) :=
  (((((h.touch _).touch _).touch _).touch _).touch _).touch _

theorem writeItem_of_touched {st₀ st : EvmYul.State .EVM} (h : Touched st₀ st) (mem : ByteArray)
    (off b : UInt256) : writeItem st mem off b = writeItem st₀ mem off b := by
  unfold writeItem
  simp only [slotW_of_touched h]

/-- **One iteration of `accum_loop`**: from the loop head with `i ≠ count`, the
machine returns to the loop head with the counter bumped, item `i` written to
memory, its six slots touched, and the active-word count still under `400`. -/
theorem drain_body {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (iW cnt head tail : UInt256) (henv : st.executionEnv = c.env) (hi : iW.toNat ≤ 63)
    (hne : iW ≠ cnt) (haw : aw.toNat ≤ 400) (hg : 36000 ≤ g.toNat) :
    ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 400 ∧ g.toNat - 36000 ≤ g'.toNat ∧
      ReachesLe depositJumpdests 130
        (at_ c st mem aw g 307 (iW :: cnt :: head :: tail :: []) e)
        (at_ c (touchItem st (base iW head))
          (writeItem st mem (UInt256.ofNat 184 * iW) (base iW head)) aw' g' 307
          ((UInt256.ofNat 1 + iW) :: cnt :: head :: tail :: []) e') := by
  obtain ⟨h0, h32, h64, h80, h96, h128, h160, h87, h86, h85, h84, h83, h82, h81⟩ := item_offsets hi
  have hcode : st.executionEnv.code = depositRuntime := hcode_of_env c henv
  have hcodeT : ∀ b, (touchItem st b).executionEnv.code = depositRuntime := fun _ => hcode
  -- 307..313 and the untaken exit test
  have h1 : ∃ (aw' g' : UInt256) (e' : Nat), aw'.toNat ≤ 400 ∧ g.toNat - 13 ≤ g'.toNat ∧
      ReachesLe depositJumpdests 5 (at_ c st mem aw g 307 (iW :: cnt :: head :: tail :: []) e)
        (at_ c st mem aw' g' 314
          (UInt256.ofNat 471 :: UInt256.eq iW cnt :: iW :: cnt :: head :: tail :: []) e') :=
    liftAt (block_step hvj_deposit deposit_b307 deposit_b307_ok (n := 5)
      deposit_b307_bound rfl (deposit_b307_shape c st mem aw g e iW cnt [head, tail]) hcode rfl
      (by gas_omega) (by simp)) haw
  have h2 := chainAt h1 fun aw g₁ e₁ haw hg₁ => liftAt
    (reach_jumpi_fallthrough deposit_s314 hcode ((eq_eq_zero_iff _ _).mpr hne) (by gas_omega) (by simp))
    haw
  clear h1
  -- 315..330: base slot, first word
  have h3 := chainAt h2 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b315 deposit_b315_ok (n := 13) deposit_b315_bound rfl
      (deposit_b315_shape c st mem aw g₁ e₁ iW cnt head [tail]) hcode rfl (by gas_omega) (by simp))
    haw
  clear h2
  have h4 := chainAt h3 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s331 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h0]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h0]; omega) (by decide)
  clear h3
  -- 332..340: second word
  have h5 := chainAt h4 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b332 deposit_b332_ok (n := 7) deposit_b332_bound rfl
      (deposit_b332_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h4
  simp only [slotW_touch] at h5
  have h6 := chainAt h5 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s341 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h32]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h32]; omega) (by decide)
  clear h5
  -- 342..351: third word, kept for the amount
  have h7 := chainAt h6 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b342 deposit_b342_ok (n := 8) deposit_b342_bound rfl
      (deposit_b342_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h6
  simp only [slotW_touch] at h7
  have h8 := chainAt h7 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s352 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h64]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h64]; omega) (by decide)
  clear h7
  -- 353..377 and the eight little-endian amount bytes
  have h9 := chainAt h8 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b353 deposit_b353_ok (n := 13) deposit_b353_bound rfl
      (deposit_b353_shape c _ _ aw g₁ e₁ _ _ [_, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h8
  have h10 := chainAt h9 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s378 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h87]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h87]; omega) (by decide)
  clear h9
  have h11 := chainAt h10 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b379 deposit_b379_ok (n := 6) deposit_b379_bound rfl
      (deposit_b379_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h10
  have h12 := chainAt h11 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s387 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h86]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h86]; omega) (by decide)
  clear h11
  have h13 := chainAt h12 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b388 deposit_b388_ok (n := 6) deposit_b388_bound rfl
      (deposit_b388_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h12
  have h14 := chainAt h13 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s396 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h85]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h85]; omega) (by decide)
  clear h13
  have h15 := chainAt h14 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b397 deposit_b397_ok (n := 6) deposit_b397_bound rfl
      (deposit_b397_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h14
  have h16 := chainAt h15 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s405 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h84]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h84]; omega) (by decide)
  clear h15
  have h17 := chainAt h16 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b406 deposit_b406_ok (n := 6) deposit_b406_bound rfl
      (deposit_b406_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h16
  have h18 := chainAt h17 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s414 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h83]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h83]; omega) (by decide)
  clear h17
  have h19 := chainAt h18 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b415 deposit_b415_ok (n := 6) deposit_b415_bound rfl
      (deposit_b415_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h18
  have h20 := chainAt h19 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s423 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h82]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h82]; omega) (by decide)
  clear h19
  have h21 := chainAt h20 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b424 deposit_b424_ok (n := 6) deposit_b424_bound rfl
      (deposit_b424_shape c _ _ aw g₁ e₁ _ _ [_, _, iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega)
      (by simp))
    haw
  clear h20
  have h22 := chainAt h21 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s432 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h81]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h81]; omega) (by decide)
  clear h21
  have h23 := chainAt h22 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore8 deposit_s433 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h80]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h80]; omega) (by decide)
  clear h22
  -- 434..462: the last three words
  have h24 := chainAt h23 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b434 deposit_b434_ok (n := 7) deposit_b434_bound rfl
      (deposit_b434_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h23
  simp only [slotW_touch] at h24
  have h25 := chainAt h24 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s443 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h96]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h96]; omega) (by decide)
  clear h24
  have h26 := chainAt h25 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b444 deposit_b444_ok (n := 7) deposit_b444_bound rfl
      (deposit_b444_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h25
  simp only [slotW_touch] at h26
  have h27 := chainAt h26 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s453 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h128]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h128]; omega) (by decide)
  clear h26
  have h28 := chainAt h27 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b454 deposit_b454_ok (n := 7) deposit_b454_bound rfl
      (deposit_b454_shape c _ _ aw g₁ e₁ _ _ [iW, cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h27
  simp only [slotW_touch] at h28
  have h29 := chainAt h28 fun aw g₁ e₁ haw hg₁ =>
    by
      refine liftAt (reach_mstore deposit_s463 (hcode_of_env c (by env_simp; exact henv)) (B := 400) haw ?_ (by decide) (M := 1515) (by decide) ?_ ?_) ?_
      · rw [h160]; omega
      · omega
      · simp
      · exact toNat_mAfter_le haw (by rw [h160]; omega) (by decide)
  clear h28
  -- 464..470: bump the counter and jump back
  have h30 := chainAt h29 fun aw g₁ e₁ haw hg₁ => liftAt
    (block_step hvj_deposit deposit_b464 deposit_b464_ok (n := 4) deposit_b464_bound rfl
      (deposit_b464_shape c _ _ aw g₁ e₁ iW [cnt, head, tail]) (hcode_of_env c (by env_simp; exact henv)) rfl (by gas_omega) (by simp))
    haw
  clear h29
  obtain ⟨aw', g', e', haw', hg', hr⟩ := h30
  exact ⟨aw', g', e', haw', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩


/-! ### The loop -/

/-- The memory after the first `i` items of a drain from head `head` have been
staged: item `j` at offset `184 · j`. -/
def drainMem (st₀ : EvmYul.State .EVM) (head : UInt256) (mem₀ : ByteArray) : Nat → ByteArray
  | 0 => mem₀
  | i + 1 => writeItem st₀ (drainMem st₀ head mem₀ i) (UInt256.ofNat 184 * UInt256.ofNat i)
      (base (UInt256.ofNat i) head)

/-- **`accum_loop` terminates after exactly `count` iterations**, with every
item staged in memory, the counter equal to the count and the six slots of each
item touched. -/
theorem drain_loop (st₀ : EvmYul.State .EVM) (henv₀ : st₀.executionEnv = c.env)
    (head tail cnt : UInt256) (mem₀ : ByteArray) (hcnt : cnt.toNat ≤ 64) :
    ∀ (m i : Nat) (st : EvmYul.State .EVM) (aw g : UInt256) (e : Nat), i + m = cnt.toNat →
      Touched st₀ st → aw.toNat ≤ 400 → 36000 * m + 25 ≤ g.toNat →
      ∃ (st' : EvmYul.State .EVM) (aw' g' : UInt256) (e' : Nat), Touched st₀ st' ∧
        aw'.toNat ≤ 400 ∧ g.toNat - (36000 * m + 25) ≤ g'.toNat ∧
        ReachesLe depositJumpdests (130 * m + 6)
          (at_ c st (drainMem st₀ head mem₀ i) aw g 307
            (UInt256.ofNat i :: cnt :: head :: tail :: []) e)
          (at_ c st' (drainMem st₀ head mem₀ cnt.toNat) aw' g' 471
            (cnt :: cnt :: head :: tail :: []) e') := by
  intro m
  induction m with
  | zero =>
    intro i st aw g e hi hst haw hg
    have hi' : i = cnt.toNat := by gas_omega
    subst hi'
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hcode := hcode_of_env c henv
    have hcnt' : UInt256.ofNat cnt.toNat = cnt := ofNat_toNat' cnt
    have h1 := block_step hvj_deposit deposit_b307 deposit_b307_ok (n := 5) deposit_b307_bound rfl
      (deposit_b307_shape c st (drainMem st₀ head mem₀ cnt.toNat) aw g e (UInt256.ofNat cnt.toNat)
        cnt [head, tail]) hcode rfl (by gas_omega) (by simp)
    have h2 := chain h1 fun g₁ e₁ hg₁ =>
      reach_jumpi_taken deposit_s314 hcode ((eq_ne_zero_iff _ _).mpr hcnt')
        (hvj_deposit 471 (by decide)) (by gas_omega) (by simp)
    obtain ⟨g', e', hg', hr⟩ := h2
    rw [hcnt'] at hr ⊢
    exact ⟨st, aw, g', e', hst, haw, by gas_omega, Reaches.le hr (by gas_omega)⟩
  | succ m ih =>
    intro i st aw g e hi hst haw hg
    have henv : st.executionEnv = c.env := hst.executionEnv.trans henv₀
    have hi63 : (UInt256.ofNat i).toNat ≤ 63 := by
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]; omega
    have hne : UInt256.ofNat i ≠ cnt := by
      intro h
      have := congrArg UInt256.toNat h
      rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
      omega
    obtain ⟨aw₁, g₁, e₁, haw₁, hg₁, hr₁⟩ :=
      drain_body c (mem := drainMem st₀ head mem₀ i) (g := g) (e := e) (UInt256.ofNat i) cnt head
        tail henv hi63 hne haw (by gas_omega)
    rw [writeItem_of_touched hst, ofNat_add_ofNat, Nat.add_comm 1 i] at hr₁
    obtain ⟨st', aw', g', e', hst', haw', hg', hr'⟩ :=
      ih (i + 1) (touchItem st (base (UInt256.ofNat i) head)) aw₁ g₁ e₁ (by gas_omega)
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
      ReachesLe depositJumpdests 20
        (at_ c st mem aw g 471 (cnt :: cnt :: headWord₀ c :: tailWord₀ c :: []) e)
        (at_ c (headStore c cnt st) mem aw g' 500 (cnt :: []) e') := by
  have hcode := hcode_of_env c henv
  have h1 := le_of_exact <| block_step hvj_deposit deposit_b471 deposit_b471_ok (n := 7)
    deposit_b471_bound rfl (deposit_b471_shape c st mem aw g e cnt cnt (headWord₀ c) (tailWord₀ c) [])
    hcode rfl (by gas_omega) (by simp)
  by_cases hfull : tailWord₀ c = headWord₀ c + cnt
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s480 hcode ((eq_ne_zero_iff _ _).mpr hfull)
        (hvj_deposit 489 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b489 deposit_b489_ok (n := 5) deposit_b489_bound rfl
        (deposit_b489_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega) (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s495 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b496 deposit_b496_ok (n := 2) deposit_b496_bound rfl
        (deposit_b496_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s499 (hcode_of_env c (by env_simp; exact henv))
        (perm_of_env c (by env_simp; exact henv) hperm) (by gas_omega) (by simp)
    clear h5
    obtain ⟨g', e', hg', hr⟩ := h6
    simp only [headStore, if_pos hfull]
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  · have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s480 hcode ((eq_eq_zero_iff _ _).mpr hfull) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b481 deposit_b481_ok (n := 2) deposit_b481_bound rfl
        (deposit_b481_shape c st mem aw g₁ e₁ cnt (headWord₀ c + cnt) []) hcode rfl (by gas_omega) (by simp)
    clear h2
    have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_sstore deposit_s484 hcode (perm_of_env c henv hperm) (by gas_omega) (by simp)
    clear h3
    have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b485 deposit_b485_ok (n := 2) deposit_b485_bound rfl
        (deposit_b485_shape c _ mem aw g₁ e₁ [cnt]) (hcode_of_env c (by env_simp; exact henv)) rfl
        (by gas_omega) (by simp)
    clear h4
    obtain ⟨g', e', hg', hr⟩ := h5
    simp only [headStore, if_neg hfull]
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩

/-- The excess word `update_excess` stores, read off the state `stX` it reads
from: `INHIBITOR` on nonempty calldata; zero when inhibited; otherwise the
folded excess above the target of `8`, or zero. -/
def newExcess (stX : EvmYul.State .EVM) : UInt256 :=
  if cdsizeWord c ≠ ⟨0⟩ then INH
  else if slotW stX (UInt256.ofNat 0) = INH then UInt256.ofNat 0
  else if UInt256.ofNat 8 < slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0) then
    (slotW stX (UInt256.ofNat 1) + slotW stX (UInt256.ofNat 0)) - UInt256.ofNat 8
  else UInt256.ofNat 0

theorem update_excess {st : EvmYul.State .EVM} {mem : ByteArray} {aw g : UInt256} {e : Nat}
    (henv : st.executionEnv = c.env) (hperm : c.env.perm = true) (cnt : UInt256)
    (hg : 50000 ≤ g.toNat) :
    ∃ (stX : EvmYul.State .EVM) (g' : UInt256) (e' : Nat), Touched st stX ∧
      g.toNat - 50000 ≤ g'.toNat ∧
      ReachesLe depositJumpdests 36 (at_ c st mem aw g 500 (cnt :: []) e)
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
          (UInt256.ofNat 0)) mem aw g' 623 (UInt256.ofNat 0 :: (UInt256.ofNat 184 * cnt) :: []) e') := by
  have hcode := hcode_of_env c henv
  have hcds : cdsizeW st = cdsizeWord c := by unfold cdsizeW; rw [henv]; rfl
  have h1 := le_of_exact <| block_step hvj_deposit deposit_b500 deposit_b500_ok (n := 3)
    deposit_b500_bound rfl (deposit_b500_shape c st mem aw g e [cnt]) hcode rfl (by gas_omega) (by simp)
  simp only [hcds] at h1
  -- the tail from `store_excess` (612), shared by every branch
  have tail : ∀ (stX : EvmYul.State .EVM) (v g₁ : UInt256) (e₁ : Nat), Touched st stX →
      g₁.toNat ≥ g.toNat - 5000 →
      ∃ (g' : UInt256) (e' : Nat), g₁.toNat - 44300 ≤ g'.toNat ∧
        ReachesLe depositJumpdests 9 (at_ c stX mem aw g₁ 612 (v :: cnt :: []) e₁)
          (at_ c ((stX.sstore (UInt256.ofNat 0) v).sstore (UInt256.ofNat 1) (UInt256.ofNat 0)) mem aw
            g' 623 (UInt256.ofNat 0 :: (UInt256.ofNat 184 * cnt) :: []) e') := by
    intro stX v g₁ e₁ hstX hg₁
    have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henv
    have hcodeX := hcode_of_env c henvX
    have t1 := le_of_exact <| block_step hvj_deposit deposit_b612 deposit_b612_ok (n := 2)
      deposit_b612_bound rfl (deposit_b612_shape c stX mem aw g₁ e₁ [v, cnt]) hcodeX rfl (by gas_omega)
      (by simp)
    have t2 := chainLe t1 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore deposit_s614 hcodeX (perm_of_env c henvX hperm) (by gas_omega) (by simp)
    clear t1
    have t3 := chainLe t2 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_deposit deposit_b615 deposit_b615_ok (n := 2) deposit_b615_bound rfl
        (deposit_b615_shape c _ mem aw g₂ e₂ [cnt]) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t2
    have t4 := chainLe t3 fun g₂ e₂ hg₂ => le_of_exact <|
      reach_sstore deposit_s618 (hcode_of_env c (by env_simp; exact henvX))
        (perm_of_env c (by env_simp; exact henvX) hperm) (by gas_omega) (by simp)
    clear t3
    have t5 := chainLe t4 fun g₂ e₂ hg₂ => le_of_exact <|
      block_step hvj_deposit deposit_b619 deposit_b619_ok (n := 3) deposit_b619_bound rfl
        (deposit_b619_shape c _ mem aw g₂ e₂ cnt []) (hcode_of_env c (by env_simp; exact henvX)) rfl
        (by gas_omega) (by simp)
    clear t4
    obtain ⟨g', e', hg', hr⟩ := t5
    exact ⟨g', e', by gas_omega, ReachesLe.mono hr (by gas_omega)⟩
  by_cases hcd : cdsizeWord c ≠ ⟨0⟩
  · -- nonempty calldata: latch the inhibitor
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_taken deposit_s505 hcode hcd (hvj_deposit 578 (by decide)) (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b578 deposit_b578_ok (n := 2) deposit_b578_bound rfl
        (deposit_b578_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h3
    obtain ⟨g', e', hg', hr'⟩ := tail st INH g₁ e₁ (Touched.refl st) (by gas_omega)
    refine ⟨st, g', e', Touched.refl st, by gas_omega, ?_⟩
    simp only [newExcess, if_pos hcd]
    exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
  · have hcd' : cdsizeWord c = ⟨0⟩ := by
      by_contra h; exact hcd h
    have h2 := chainLe h1 fun g₁ e₁ hg₁ => le_of_exact <|
      reach_jumpi_fallthrough deposit_s505 hcode hcd' (by gas_omega) (by simp)
    clear h1
    have h3 := chainLe h2 fun g₁ e₁ hg₁ => le_of_exact <|
      block_step hvj_deposit deposit_b506 deposit_b506_ok (n := 8) deposit_b506_bound rfl
        (deposit_b506_shape c st mem aw g₁ e₁ [cnt]) hcode rfl (by gas_omega) (by simp)
    clear h2
    simp only [slotW_touch] at h3
    have hstX : Touched st (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)) :=
      ((Touched.refl st).touch _).touch _
    have hcodeX : (touch (touch st (UInt256.ofNat 0)) (UInt256.ofNat 1)).executionEnv.code
        = depositRuntime := hcode
    by_cases hinh : slotW st (UInt256.ofNat 0) = INH
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_taken deposit_s549 hcodeX ((eq_ne_zero_iff _ _).mpr hinh.symm)
          (hvj_deposit 560 (by decide)) (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_deposit deposit_b560 deposit_b560_ok (n := 6) deposit_b560_bound rfl
          (deposit_b560_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h5
      obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
      refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
      simp only [newExcess, if_neg hcd, slotW_touch, if_pos hinh]
      exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
    · have h4 := chainLe h3 fun g₁ e₁ hg₁ => le_of_exact <|
        reach_jumpi_fallthrough deposit_s549 hcodeX ((eq_eq_zero_iff _ _).mpr (fun h => hinh h.symm))
          (by gas_omega) (by simp)
      clear h3
      have h5 := chainLe h4 fun g₁ e₁ hg₁ => le_of_exact <|
        block_step hvj_deposit deposit_b550 deposit_b550_ok (n := 6) deposit_b550_bound rfl
          (deposit_b550_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
      clear h4
      by_cases hgt : UInt256.ofNat 8 < slotW st (UInt256.ofNat 1) + slotW st (UInt256.ofNat 0)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_taken deposit_s559 hcodeX ((gt_ne_zero_iff _ _).mpr hgt)
            (hvj_deposit 568 (by decide)) (by gas_omega) (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_deposit deposit_b568 deposit_b568_ok (n := 7) deposit_b568_bound rfl
            (deposit_b568_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ _ g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_pos hgt]
        exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)
      · have h6 := chainLe h5 fun g₁ e₁ hg₁ => le_of_exact <|
          reach_jumpi_fallthrough deposit_s559 hcodeX ((gt_eq_zero_iff _ _).mpr hgt) (by gas_omega)
            (by simp)
        clear h5
        have h7 := chainLe h6 fun g₁ e₁ hg₁ => le_of_exact <|
          block_step hvj_deposit deposit_b560 deposit_b560_ok (n := 6) deposit_b560_bound rfl
            (deposit_b560_shape c _ mem aw g₁ e₁ _ _ [cnt]) hcodeX rfl (by gas_omega) (by simp)
        clear h6
        obtain ⟨g₁, e₁, hg₁, hr₁⟩ := h7
        obtain ⟨g', e', hg', hr'⟩ := tail _ (UInt256.ofNat 0) g₁ e₁ hstX (by gas_omega)
        refine ⟨_, g', e', hstX, by gas_omega, ?_⟩
        simp only [newExcess, if_neg hcd, slotW_touch, if_neg hinh, if_neg hgt]
        exact ReachesLe.mono (hr₁.trans hr') (by gas_omega)

/-! ### The system endpoint -/

theorem drainWord_le : (drainWord c).toNat ≤ 64 := by
  unfold drainWord
  split
  · rename_i h
    have := (toNat_lt_iff _ _).mp h
    rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)] at this
    omega
  · rw [toNat_ofNat_of_lt (by rw [size_eq]; omega)]

theorem touched_stP : Touched (entrySt c) (stP c) := ((Touched.refl _).touch _).touch _

/-- **The system call returns.** For `SYSTEM_ADDR` with write permission, the
run drains `min(tail − head, 64)` items into memory, rewrites the four control
words, and halts on `RETURN` publishing the staged records. -/
theorem system_returns (hsys : callerWord c = sysW) (hperm : c.env.perm = true)
    (hg : 2500000 ≤ c.gas.toNat) :
    ∃ (st' stX : EvmYul.State .EVM) (aw g : UInt256) (e : Nat),
      Touched (entrySt c) st' ∧ Touched (headStore c (drainWord c) st') stX ∧
      Ends c 8500
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw g 623
          (UInt256.ofNat 0 :: (UInt256.ofNat 184 * drainWord c) :: []) e) .RETURN
        ((drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat).readWithPadding 0
          (UInt256.ofNat 184 * drainWord c).toNat) := by
  obtain ⟨g₀, e₀, hg₀, hpre⟩ := system_prefix c hsys (by gas_omega)
  have hcnt := drainWord_le c
  obtain ⟨st', aw', g₁, e₁, hst', haw', hg₁, hloop⟩ := drain_loop c (entrySt c) rfl (headWord₀ c)
    (tailWord₀ c) (drainWord c) (mem₀ c) hcnt (drainWord c).toNat 0 (stP c) (aw₀ c) g₀ e₀
    (by gas_omega) (touched_stP c) (by rw [activeWords_entry]; omega) (by gas_omega)
  have h1 : ∃ (g : UInt256) (e : Nat), c.gas.toNat - 2308400 ≤ g.toNat ∧
      ReachesLe depositJumpdests 8351 c.entry
        (at_ c st' (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 471
          (drainWord c :: drainWord c :: headWord₀ c :: tailWord₀ c :: []) e) :=
    ⟨g₁, e₁, by gas_omega, ReachesLe.mono (hpre.trans hloop) (by gas_omega)⟩
  have henv' : st'.executionEnv = c.env := hst'.executionEnv
  have h2 := chainLe h1 fun g e hg => update_head c henv' hperm (drainWord c) (by gas_omega)
  clear h1
  have henvH : (headStore c (drainWord c) st').executionEnv = c.env := by
    unfold headStore; split <;> (env_simp; exact henv')
  have h3 : ∃ (stX : EvmYul.State .EVM) (g : UInt256) (e : Nat),
      Touched (headStore c (drainWord c) st') stX ∧ c.gas.toNat - 2402900 ≤ g.toNat ∧
      ReachesLe depositJumpdests (8351 + 20 + 36) c.entry
        (at_ c ((stX.sstore (UInt256.ofNat 0) (newExcess c stX)).sstore (UInt256.ofNat 1)
            (UInt256.ofNat 0))
          (drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) aw' g 623
          (UInt256.ofNat 0 :: (UInt256.ofNat 184 * drainWord c) :: []) e) := by
    obtain ⟨g₂, e₂, hg₂, hr₂⟩ := h2
    obtain ⟨stX, g₃, e₃, hstX, hg₃, hr₃⟩ := update_excess c
      (mem := drainMem (entrySt c) (headWord₀ c) (mem₀ c) (drainWord c).toNat) (aw := aw')
      (g := g₂) (e := e₂) henvH hperm (drainWord c) (by gas_omega)
    exact ⟨stX, g₃, e₃, hstX, by gas_omega, hr₂.trans hr₃⟩
  clear h2
  obtain ⟨stX, g, e, hstX, hgX, hr⟩ := h3
  have henvX : stX.executionEnv = c.env := hstX.executionEnv.trans henvH
  refine ⟨st', stX, aw', g, e, hst', hstX, ReachesLe.mono hr (by gas_omega), ?_⟩
  have hlen : (UInt256.ofNat 184 * drainWord c).toNat = 184 * (drainWord c).toNat :=
    toNat_ofNat_mul_of_lt 184 _ (by rw [size_eq]; omega)
  refine halt_RETURN deposit_s623 (hcode_of_env c (by env_simp; exact henvX)) (B := 400) (M := 1512)
    (g := g) haw' ?_ (by decide) (by decide) ?_ (by simp)
  · rw [hlen]; show (0 + 184 * (drainWord c).toNat + 31) / 32 ≤ 400; omega
  · omega

end Eip8282.Audit.EntryReach.Deposit
